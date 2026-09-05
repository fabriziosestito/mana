defmodule Conf.CounterHttp do
  @moduledoc """
  Minimal LiveView dead-render gate: GET /counter with a Host header that
  carries NO port (`host: t`). That path resolves the port with
  URI.default_port/1. The function returns nil unless the elixir_config URI
  table is seeded at boot. A Host header with a port (localhost:PORT) masks
  the bug, so this program pins the portless case. It prints only stable
  facts.
  """

  def go do
    port = Conf.WsClient.boot()

    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "GET /counter HTTP/1.1\r\nhost: t\r\n\r\n")
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
    :gen_tcp.close(c)

    IO.puts(status)
    IO.puts(inspect(String.contains?(body, "Count:")))
    IO.puts(inspect(String.contains?(body, "data-phx-main")))
    IO.puts(inspect(:done))
    :ok
  end

  defp read_head(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] ->
        {head, rest}

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
