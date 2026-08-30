defmodule Conf.Http.DemoPlug do
  import Plug.Conn

  def init(opts), do: opts

  def call(conn, _opts) do
    case {conn.method, conn.path_info} do
      {"GET", []} ->
        send_resp(conn, 200, "hello from mana")

      {"GET", ["json"]} ->
        conn
        |> put_resp_content_type("application/json")
        |> send_resp(200, ~s({"ok":true,"n":42}))

      {"GET", ["params"]} ->
        conn = fetch_query_params(conn)
        pairs = conn.query_params |> Enum.sort() |> Enum.map_join(",", fn {k, v} -> "#{k}=#{v}" end)
        send_resp(conn, 200, pairs)

      {"POST", ["echo"]} ->
        {:ok, body, conn} = read_body(conn)
        send_resp(conn, 200, "echo:" <> body)

      _ ->
        send_resp(conn, 404, "nope")
    end
  end
end

defmodule Conf.Http do
  @moduledoc """
  Bandit + Plug compiled from hex, serving HTTP/1.1 over our gen_tcp —
  exercised with a raw socket client. Printed: status line, deterministic
  headers (content-type/length, server — same bandit version on both
  runtimes), body. Never the date header. Includes keep-alive (two
  requests, one connection), POST body, 404, connection: close.
  """

  def go do
    :logger.remove_handler(:default)

    children = [
      {Bandit,
       plug: Conf.Http.DemoPlug,
       scheme: :http,
       port: 0,
       startup_log: false,
       http_options: [compress: false],
       http_2_options: [enabled: false],
       thousand_island_options: [num_acceptors: 2]}
    ]

    {:ok, sup} = Supervisor.start_link(children, strategy: :one_for_one)
    [{_, bandit_pid, _, _}] = Supervisor.which_children(sup)
    {:ok, {_ip, port}} = ThousandIsland.listener_info(bandit_pid)
    IO.puts(inspect(port > 0))

    # keep-alive: two GETs on one connection
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "GET / HTTP/1.1\r\nhost: t\r\n\r\n")
    print_response(c)
    :ok = :gen_tcp.send(c, "GET /json HTTP/1.1\r\nhost: t\r\n\r\n")
    print_response(c)
    :ok = :gen_tcp.close(c)

    # POST with body, connection: close
    {:ok, c2} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])

    :ok =
      :gen_tcp.send(c2, [
        "POST /echo HTTP/1.1\r\nhost: t\r\ncontent-length: 9\r\nconnection: close\r\n\r\n",
        "some body"
      ])

    print_response(c2)
    IO.puts(inspect(:gen_tcp.recv(c2, 1, 200)))
    :ok = :gen_tcp.close(c2)

    # query params + 404
    {:ok, c3} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c3, "GET /params?b=2&a=1 HTTP/1.1\r\nhost: t\r\n\r\n")
    print_response(c3)
    :ok = :gen_tcp.send(c3, "GET /missing HTTP/1.1\r\nhost: t\r\n\r\n")
    print_response(c3)
    :ok = :gen_tcp.close(c3)

    IO.puts(inspect(:done))
    :ok
  end

  # read status line + headers (until CRLFCRLF), then content-length body;
  # print status line, sorted deterministic headers, body
  defp print_response(sock) do
    {head, leftover} = read_head(sock, "")
    [status | header_lines] = String.split(head, "\r\n", trim: true)

    headers =
      header_lines
      |> Enum.map(fn l ->
        [k, v] = String.split(l, ": ", parts: 2)
        {String.downcase(k), v}
      end)
      |> Map.new()

    len = String.to_integer(Map.get(headers, "content-length", "0"))
    body = read_body_bytes(sock, leftover, len)

    IO.puts(status)

    for k <- ["content-type", "content-length", "server", "connection", "vary"] do
      case Map.fetch(headers, k) do
        {:ok, v} -> IO.puts("#{k}: #{v}")
        :error -> :ok
      end
    end

    IO.puts("body=#{body}")
    IO.puts("--")
  end

  defp read_head(sock, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] ->
        {head, rest}

      _ ->
        {:ok, chunk} = :gen_tcp.recv(sock, 0, 5000)
        read_head(sock, acc <> chunk)
    end
  end

  defp read_body_bytes(_sock, buf, len) when byte_size(buf) >= len,
    do: binary_part(buf, 0, len)

  defp read_body_bytes(sock, buf, len) do
    {:ok, more} = :gen_tcp.recv(sock, len - byte_size(buf), 5000)
    read_body_bytes(sock, buf <> more, len)
  end
end
