defmodule Bench.Http.HelloPlug do
  import Plug.Conn

  def init(opts), do: opts
  def call(conn, _opts), do: send_resp(conn, 200, "hello world")
end

defmodule Bench.Http do
  @moduledoc """
  Compiled Bandit serving HTTP/1.1, measured with a raw gen_tcp client:
  full connect+GET+close cycles and keep-alive GETs on one connection.
  This is the compiled-Bandit datapoint for the native-server discussion.
  """

  @req "GET / HTTP/1.1\r\nhost: bench\r\n\r\n"

  def run do
    :logger.remove_handler(:default)

    {:ok, bandit} =
      Bandit.start_link(
        plug: Bench.Http.HelloPlug,
        scheme: :http,
        port: 0,
        startup_log: false,
        http_options: [compress: false],
        http_2_options: [enabled: false]
      )

    {:ok, {_ip, port}} = ThousandIsland.listener_info(bandit)

    Benchee.run(
      %{
        "http GET (new conn)" => fn ->
          {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
          :ok = :gen_tcp.send(c, @req)
          read_response(c, "")
          :ok = :gen_tcp.close(c)
        end,
        "http GET (keepalive)" => {
          fn c ->
            :ok = :gen_tcp.send(c, @req)
            read_response(c, "")
            c
          end,
          before_scenario: fn _ ->
            {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
            c
          end
        }
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end

  # read until we have headers + the 11-byte body ("hello world")
  defp read_response(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [_head, body] when byte_size(body) >= 11 ->
        :ok

      _ ->
        {:ok, chunk} = :gen_tcp.recv(c, 0, 5000)
        read_response(c, acc <> chunk)
    end
  end
end
