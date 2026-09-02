defmodule Bench.Ws do
  @moduledoc """
  Phoenix LiveView over a websocket, measured with a raw gen_tcp client:
  a full mount+join per connection, and the interactive event round-trip
  (phx-click -> diff reply) on a kept-alive socket.
  """

  @secret String.duplicate("mana-secret!", 6)
  @ws_key "AQIDBAUGBwgJCgsMDQ4PEA=="

  def run do
    port = boot()
    IO.puts("Bench.Ws: #{Bench.Env.tag()}")
    bench(port)
  end

  @doc "Boot the Phoenix app on a free port with the runtime-selected adapter/JSON; returns the port."
  def boot do
    :logger.remove_handler(:default)
    Application.put_env(:plug, :validate_header_keys_during_test, false)
    Application.put_env(:phoenix, :json_library, Bench.Env.json_library())

    Application.put_env(:phx_app, PhxAppWeb.Endpoint,
      adapter: Bench.Env.http_adapter(),
      http: [ip: {127, 0, 0, 1}, port: 0],
      server: true,
      secret_key_base: @secret,
      live_view: [signing_salt: "rl9uueu0"],
      render_errors: [formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON], layout: false]
    )

    {:ok, _} = Plug.Application.start(:normal, [])
    {:ok, _} = Plug.Crypto.Application.start(:normal, [])
    {:ok, _} = Phoenix.PubSub.Application.start(:normal, [])
    {:ok, _} = PhxApp.Application.start(:normal, [])
    {:ok, {_ip, port}} = PhxAppWeb.Endpoint.server_info(:http)
    port
  end

  defp bench(port) do
    Benchee.run(
      %{
        "lv mount+join (new conn)" => fn ->
          {sock, _topic} = join(port)
          :gen_tcp.close(sock)
        end,
        "lv event roundtrip (keepalive)" =>
          {fn {sock, topic} -> click(sock, topic) end,
           before_scenario: fn _ -> join(port) end,
           after_scenario: fn {sock, _} -> :gen_tcp.close(sock) end}
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end

  @doc "Dead-render /counter, upgrade, phx_join; returns {socket, topic}."
  def join(port) do
    {headers, body} = get(port, "/counter")
    tokens = extract(headers, body)
    sock = upgrade(port, tokens)
    topic = "lv:" <> tokens.id

    payload = %{
      "url" => "http://localhost:#{port}/counter",
      "params" => %{"_csrf_token" => tokens.csrf, "_mounts" => 0},
      "session" => tokens.session,
      "static" => tokens.static
    }

    push(sock, "1", "1", topic, "phx_join", payload)
    {[_, _, ^topic, "phx_reply", _reply], _} = recv_msg(sock)
    {sock, topic}
  end

  @doc "One phx-click event round-trip on a joined socket."
  def click(sock, topic) do
    push(sock, "1", "2", topic, "event", %{"type" => "click", "event" => "inc", "value" => %{}})
    {[_, _, ^topic, "phx_reply", _ev], _} = recv_msg(sock)
    :ok
  end

  defp get(port, path) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "GET #{path} HTTP/1.1\r\nhost: b\r\n\r\n")
    {headers, leftover} = read_head(c)
    len = String.to_integer(Map.get(headers, "content-length", "0"))
    body = read_body(c, leftover, len)
    :gen_tcp.close(c)
    {headers, body}
  end

  defp extract(_headers, body) do
    [_, csrf] = Regex.run(~r/name="csrf-token" content="([^"]+)"/, body)
    [main] = Regex.run(~r/<div[^>]*data-phx-main[^>]*>/, body)
    [_, id] = Regex.run(~r/id="([^"]+)"/, main)
    [_, session] = Regex.run(~r/data-phx-session="([^"]+)"/, main)
    [_, static] = Regex.run(~r/data-phx-static="([^"]*)"/, main)
    %{csrf: csrf, id: id, session: session, static: static}
  end

  defp upgrade(port, tokens) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    qs = "vsn=2.0.0&_csrf_token=#{URI.encode_www_form(tokens.csrf)}&_mounts=0"

    req = [
      "GET /live/websocket?#{qs} HTTP/1.1\r\n",
      "host: b\r\nupgrade: websocket\r\nconnection: Upgrade\r\n",
      "sec-websocket-key: #{@ws_key}\r\nsec-websocket-version: 13\r\n\r\n"
    ]

    :ok = :gen_tcp.send(c, req)
    {_headers, _leftover} = read_head(c)
    c
  end

  # The client's own JSON work must not dominate the measurement: use the
  # runtime-selected library (native serde natively, Jason on BEAM) so the
  # client costs about the same on both runtimes.
  defp json, do: Bench.Env.json_library()

  defp push(c, join_ref, ref, topic, event, payload) do
    text = json().encode!([join_ref, ref, topic, event, payload])
    len = byte_size(text)

    len_part =
      cond do
        len < 126 -> <<1::1, len::7>>
        len < 65_536 -> <<1::1, 126::7, len::16>>
        true -> <<1::1, 127::7, len::64>>
      end

    :ok = :gen_tcp.send(c, [<<1::1, 0::3, 1::4>>, len_part, <<0, 0, 0, 0>>, text])
  end

  defp recv_msg(c, buf \\ <<>>) do
    <<_fin::1, _rsv::3, 1::4, 0::1, len7::7, rest::binary>> = need(c, buf, 2)

    {len, rest} =
      case len7 do
        126 ->
          <<l::16, r::binary>> = need(c, rest, 2)
          {l, r}

        127 ->
          <<l::64, r::binary>> = need(c, rest, 8)
          {l, r}

        l ->
          {l, rest}
      end

    <<payload::binary-size(len), rest::binary>> = need(c, rest, len)
    {json().decode!(payload), rest}
  end

  defp need(_c, buf, n) when byte_size(buf) >= n, do: buf

  defp need(c, buf, n) do
    {:ok, more} = :gen_tcp.recv(c, 0, 5000)
    need(c, buf <> more, n)
  end

  defp read_head(c, acc \\ "") do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] ->
        [_status | lines] = String.split(head, "\r\n", trim: true)

        headers =
          lines
          |> Enum.map(fn l ->
            [k, v] = String.split(l, ": ", parts: 2)
            {String.downcase(k), v}
          end)
          |> Map.new()

        {headers, rest}

      _ ->
        {:ok, chunk} = :gen_tcp.recv(c, 0, 5000)
        read_head(c, acc <> chunk)
    end
  end

  defp read_body(_c, buf, len) when byte_size(buf) >= len, do: binary_part(buf, 0, len)

  defp read_body(c, buf, len) do
    {:ok, more} = :gen_tcp.recv(c, len - byte_size(buf), 5000)
    read_body(c, buf <> more, len)
  end
end
