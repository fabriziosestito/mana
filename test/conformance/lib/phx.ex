defmodule Conf.Phx do
  @moduledoc """
  A scaffolded `mix phx.new` app (examples/phoenix/phx_app) that serves its
  landing page natively. Config files never run at runtime (closed world).
  This program seeds the endpoint env, identically on both runtimes. The
  BEAM oracle also runs without Mix config. The CSRF token and the session
  cookie are random, so only stable response facts print.
  """

  @secret String.duplicate("mana-secret!", 6)

  def go do
    if System.get_env("PHX_KEEP_LOGGER") == nil, do: :logger.remove_handler(:default)

    # The .app-resource env defaults never load in the closed world, and
    # the bare `elixir -pa` run of the oracle does not load them either.
    # Seed what the request path fetches.
    Application.put_env(:plug, :validate_header_keys_during_test, false)

    Application.put_env(:phx_app, PhxAppWeb.Endpoint,
      adapter: Bandit.PhoenixAdapter,
      http: [ip: {127, 0, 0, 1}, port: 0],
      server: true,
      secret_key_base: @secret,
      render_errors: [
        formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
        layout: false
      ]
    )

    # Closed world: the program starts the application trees explicitly.
    # The BEAM oracle also runs without the Mix app boot. The phoenix_pubsub
    # app is :pg.start_link(Phoenix.PubSub).
    {:ok, _} = Plug.Application.start(:normal, [])
    {:ok, _} = Phoenix.PubSub.Application.start(:normal, [])
    {:ok, _} = PhxApp.Application.start(:normal, [])
    {:ok, {_ip, port}} = PhxAppWeb.Endpoint.server_info(:http)
    IO.puts(inspect(port > 0))

    # landing page
    {status, headers, body} = request(port, "GET / HTTP/1.1\r\nhost: t\r\n\r\n")
    IO.puts(status)
    IO.puts("content-type: #{Map.get(headers, "content-type")}")
    IO.puts(inspect(String.contains?(body, "Phoenix Framework")))
    IO.puts(inspect(String.contains?(body, "<meta name=\"csrf-token\"")))
    IO.puts(inspect(String.contains?(body, "Guides")))
    IO.puts(inspect(Map.has_key?(headers, "set-cookie")))

    # 404 route
    {status2, _h2, body2} = request(port, "GET /nope HTTP/1.1\r\nhost: t\r\n\r\n")
    IO.puts(status2)
    IO.puts(inspect(String.contains?(body2, "Not Found")))

    IO.puts(inspect(:done))
    :ok
  end

  defp request(port, req) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, req)
    {head, leftover} = read_head(c, "")
    [status | header_lines] = String.split(head, "\r\n", trim: true)

    headers =
      header_lines
      |> Enum.map(fn l ->
        [k, v] = String.split(l, ": ", parts: 2)
        {String.downcase(k), v}
      end)
      |> Map.new()

    len = String.to_integer(Map.get(headers, "content-length", "0"))
    body = read_body(c, leftover, len)
    :ok = :gen_tcp.close(c)
    {status, headers, body}
  end

  defp read_head(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] -> {head, rest}
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
