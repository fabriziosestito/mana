defmodule Conf.Ti.Echo do
  use ThousandIsland.Handler

  @impl ThousandIsland.Handler
  def handle_data(data, socket, state) do
    ThousandIsland.Socket.send(socket, data)
    {:continue, state}
  end
end

defmodule Conf.Ti do
  @moduledoc """
  ThousandIsland compiled from hex, with a real echo socket. The program
  covers the acceptor pool supervision tree, the handler GenServers, the
  interleave of active :once and passive recv, and the getstat teardown.
  It does exact-length recvs only.
  """

  def go do
    :logger.remove_handler(:default)

    {:ok, server} =
      ThousandIsland.start_link(
        port: 0,
        handler_module: Conf.Ti.Echo,
        num_acceptors: 2
      )

    {:ok, {_ip, port}} = ThousandIsland.listener_info(server)
    IO.puts(inspect(port > 0))

    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "hello ti")
    IO.puts(inspect(:gen_tcp.recv(c, 8)))

    :ok = :gen_tcp.send(c, "second")
    IO.puts(inspect(:gen_tcp.recv(c, 6)))
    :ok = :gen_tcp.close(c)

    # two concurrent connections
    {:ok, a} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    {:ok, b} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(a, "aa")
    :ok = :gen_tcp.send(b, "bb")
    IO.puts(inspect(:gen_tcp.recv(a, 2)))
    IO.puts(inspect(:gen_tcp.recv(b, 2)))
    :ok = :gen_tcp.close(a)
    :ok = :gen_tcp.close(b)

    :ok = ThousandIsland.stop(server)
    IO.puts(inspect(:stopped))
    :ok
  end
end
