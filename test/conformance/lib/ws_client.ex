defmodule Conf.WsClient do
  @moduledoc """
  Pure-Elixir websocket client that drives a Phoenix LiveView over a raw
  :gen_tcp socket. The WS conformance programs share it. Everything is
  deterministic on purpose. The Sec-WebSocket-Key is fixed. The mask key is
  a fixed all-zero key, which RFC 6455 allows, so the masked payload equals
  the plain payload. Replies are Jason-decoded before they print, so the
  JSON key order never leaks into the byte-diff.
  """

  @secret String.duplicate("mana-secret!", 6)
  @ws_key "AQIDBAUGBwgJCgsMDQ4PEA=="
  @ws_guid "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

  # The same closed-world boot as Conf.Phx: seed the endpoint env and start
  # the application trees explicitly. The BEAM oracle also runs without
  # Mix config.
  def boot do
    if System.get_env("PHX_KEEP_LOGGER") == nil, do: :logger.remove_handler(:default)

    Application.put_env(:plug, :validate_header_keys_during_test, false)
    # Native JSON on the Phoenix socket serializer path: ManaJSON (serde) on
    # the native binary, Jason on the BEAM oracle, where ManaJSON cannot run.
    # This proves that ManaJSON is a drop-in for the LiveView serializer.
    Application.put_env(:phoenix, :json_library, Conf.JSON.lib())

    Application.put_env(:phx_app, PhxAppWeb.Endpoint,
      adapter: Bandit.PhoenixAdapter,
      http: [ip: {127, 0, 0, 1}, port: 0],
      server: true,
      secret_key_base: @secret,
      live_view: [signing_salt: "rl9uueu0"],
      render_errors: [
        formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
        layout: false
      ]
    )

    {:ok, _} = Plug.Application.start(:normal, [])
    # LiveView signs its session and static tokens with Plug.Crypto.sign.
    # Its key cache defaults to the Plug.Crypto.Keys ETS table, which is a
    # different table from Plug.Keys (the one that Plug.Session uses). The
    # app that owns it never starts in the closed world, so start it here.
    {:ok, _} = Plug.Crypto.Application.start(:normal, [])
    {:ok, _} = Phoenix.PubSub.Application.start(:normal, [])
    {:ok, _} = PhxApp.Application.start(:normal, [])
    {:ok, {_ip, port}} = PhxAppWeb.Endpoint.server_info(:http)
    port
  end

  @doc "GET a page over a throwaway connection. Returns {status, headers, body}."
  def get(port, path) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "GET #{path} HTTP/1.1\r\nhost: localhost:#{port}\r\n\r\n")
    {status, headers, leftover} = read_response_head(c)
    len = String.to_integer(Map.get(headers, "content-length", "0"))
    body = read_body(c, leftover, len)
    :ok = :gen_tcp.close(c)
    {status, headers, body}
  end

  @doc """
  Pulls the LiveView bootstrap data out of a dead-rendered page. The data
  is the csrf token, the session cookie, the main element id, and the phx
  session and static tokens.
  """
  def extract(headers, body) do
    [_, csrf] = Regex.run(~r/name="csrf-token" content="([^"]+)"/, body)
    [main] = Regex.run(~r/<div[^>]*data-phx-main[^>]*>/, body)
    [_, id] = Regex.run(~r/id="([^"]+)"/, main)
    [_, session] = Regex.run(~r/data-phx-session="([^"]+)"/, main)
    [_, static] = Regex.run(~r/data-phx-static="([^"]*)"/, main)

    cookie =
      headers
      |> Map.get("set-cookie", "")
      |> String.split(";", parts: 2)
      |> hd()

    %{csrf: csrf, id: id, session: session, static: static, cookie: cookie}
  end

  @doc """
  Opens a socket and performs the websocket upgrade on /live/websocket.
  Returns {socket, resp_headers, accept_ok?}. `extra_headers` is an
  iolist that the function appends to the request, for example an
  extensions offer.
  """
  def upgrade(port, tokens, extra_headers \\ []) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    qs = "vsn=2.0.0&_csrf_token=#{URI.encode_www_form(tokens.csrf)}&_mounts=0"

    req = [
      "GET /live/websocket?#{qs} HTTP/1.1\r\n",
      "host: localhost:#{port}\r\n",
      "upgrade: websocket\r\n",
      "connection: Upgrade\r\n",
      "sec-websocket-key: #{@ws_key}\r\n",
      "sec-websocket-version: 13\r\n",
      "cookie: #{tokens.cookie}\r\n",
      extra_headers,
      "\r\n"
    ]

    :ok = :gen_tcp.send(c, req)
    {status, headers, _leftover} = read_response_head(c)

    expected = Base.encode64(:crypto.hash(:sha, @ws_key <> @ws_guid))
    accept_ok = Map.get(headers, "sec-websocket-accept") == expected
    {c, status, headers, accept_ok}
  end

  # Frame codec, client side. Server frames arrive unmasked.

  @doc "Sends a masked text frame with an all-zero mask key."
  def send_text(c, payload), do: send_frame(c, 1, payload)

  def send_close(c), do: send_frame(c, 8, <<1000::16>>)

  defp send_frame(c, opcode, payload) do
    len = byte_size(payload)

    len_part =
      cond do
        len < 126 -> <<1::1, len::7>>
        len < 65_536 -> <<1::1, 126::7, len::16>>
        true -> <<1::1, 127::7, len::64>>
      end

    frame = [<<1::1, 0::3, opcode::4>>, len_part, <<0, 0, 0, 0>>, payload]
    :ok = :gen_tcp.send(c, frame)
  end

  @doc """
  Receives one complete data frame. Returns {opcode, rsv1, payload, rest}.
  Pings are answered and skipped. Fragmented messages are reassembled.
  rsv1 comes from the first frame, because permessage-deflate marks the
  message there.
  """
  def recv_frame(c, buf \\ <<>>) do
    {fin, rsv1, opcode, payload, rest} = read_one(c, buf)

    cond do
      opcode == 9 ->
        send_frame(c, 10, payload)
        recv_frame(c, rest)

      fin == 0 ->
        {full, rest2} = recv_continuations(c, rest, payload)
        {opcode, rsv1, full, rest2}

      true ->
        {opcode, rsv1, payload, rest}
    end
  end

  defp recv_continuations(c, buf, acc) do
    {fin, _rsv1, _opcode, payload, rest} = read_one(c, buf)

    if fin == 1 do
      {acc <> payload, rest}
    else
      recv_continuations(c, rest, acc <> payload)
    end
  end

  defp read_one(c, buf) do
    <<fin::1, rsv1::1, _rsv::2, opcode::4, masked::1, len7::7, rest::binary>> = need(c, buf, 2)

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

    0 = masked
    <<payload::binary-size(len), rest::binary>> = need(c, rest, len)
    {fin, rsv1, opcode, payload, rest}
  end

  defp need(_c, buf, n) when byte_size(buf) >= n, do: buf

  defp need(c, buf, n) do
    {:ok, more} = :gen_tcp.recv(c, 0, 5000)
    need(c, buf <> more, n)
  end

  # Phoenix V2 serializer over text frames.

  @doc "Sends a V2 message [join_ref, ref, topic, event, payload]."
  def push(c, join_ref, ref, topic, event, payload) do
    send_text(c, Jason.encode!([join_ref, ref, topic, event, payload]))
  end

  @doc "Receives and decodes one V2 text message."
  def recv_msg(c, buf \\ <<>>) do
    {opcode, _rsv1, payload, rest} = recv_frame(c, buf)
    1 = opcode
    {Jason.decode!(payload), rest}
  end

  # permessage-deflate (RFC 7692).

  @doc """
  A pair of raw zlib streams (headerless, window 15) with context
  takeover. This matches the default negotiation of Bandit. One stream
  inflates server frames, and one deflates client frames.
  """
  def deflate_ctx do
    zi = :zlib.open()
    :zlib.inflateInit(zi, -15)
    zd = :zlib.open()
    :zlib.deflateInit(zd, :default, :deflated, -15, 8, :default)
    %{inflate: zi, deflate: zd}
  end

  @doc "Sends a compressed V2 message: deflate, strip the tail, and set RSV1."
  def push_deflate(c, ctx, join_ref, ref, topic, event, payload) do
    json = Jason.encode!([join_ref, ref, topic, event, payload])
    comp = IO.iodata_to_binary(:zlib.deflate(ctx.deflate, json, :sync))
    # Drop the trailing 00 00 FF FF sync marker (RFC 7692 §7.2.1).
    body = binary_part(comp, 0, byte_size(comp) - 4)
    send_frame_rsv1(c, 1, body)
  end

  @doc "Receives and decodes one V2 message. Inflates it if RSV1 is set."
  def recv_msg_deflate(c, ctx, buf \\ <<>>) do
    {opcode, rsv1, payload, rest} = recv_frame(c, buf)
    1 = opcode

    data =
      if rsv1 == 1 do
        drain(ctx.inflate, <<payload::binary, 0, 0, 255, 255>>)
      else
        payload
      end

    {Jason.decode!(data), rsv1, rest}
  end

  defp drain(z, data) do
    case :zlib.safeInflate(z, data) do
      {:continue, out} -> IO.iodata_to_binary([out, drain(z, [])])
      {:finished, out} -> IO.iodata_to_binary(out)
    end
  end

  defp send_frame_rsv1(c, opcode, payload) do
    len = byte_size(payload)

    len_part =
      cond do
        len < 126 -> <<1::1, len::7>>
        len < 65_536 -> <<1::1, 126::7, len::16>>
        true -> <<1::1, 127::7, len::64>>
      end

    # fin=1, rsv1=1 (compressed), rsv2=rsv3=0.
    frame = [<<1::1, 1::1, 0::2, opcode::4>>, len_part, <<0, 0, 0, 0>>, payload]
    :ok = :gen_tcp.send(c, frame)
  end

  @doc "Joins the LiveView channel. Returns {topic, reply_payload, rest}."
  def join(c, port, path, tokens, join_ref) do
    topic = "lv:" <> tokens.id

    payload = %{
      "url" => "http://localhost:#{port}#{path}",
      "params" => %{"_csrf_token" => tokens.csrf, "_mounts" => 0},
      "session" => tokens.session,
      "static" => tokens.static
    }

    push(c, join_ref, join_ref, topic, "phx_join", payload)
    {[^join_ref, ^join_ref, ^topic, "phx_reply", reply], rest} = recv_msg(c)
    {topic, reply, rest}
  end

  # HTTP response head parsing, shared with the upgrade.

  defp read_response_head(c), do: read_response_head(c, "")

  defp read_response_head(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] ->
        [status | header_lines] = String.split(head, "\r\n", trim: true)

        headers =
          header_lines
          |> Enum.map(fn l ->
            [k, v] = String.split(l, ": ", parts: 2)
            {String.downcase(k), v}
          end)
          |> Map.new()

        {status, headers, rest}

      _ ->
        {:ok, chunk} = :gen_tcp.recv(c, 0, 5000)
        read_response_head(c, acc <> chunk)
    end
  end

  defp read_body(_c, buf, len) when byte_size(buf) >= len, do: binary_part(buf, 0, len)

  defp read_body(c, buf, len) do
    {:ok, more} = :gen_tcp.recv(c, len - byte_size(buf), 5000)
    read_body(c, buf <> more, len)
  end
end
