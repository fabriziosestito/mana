defmodule Conf.Tcp do
  @moduledoc """
  gen_tcp passive mode over loopback: listen on an ephemeral port (never
  printed), an echo server process, exact-length recvs (TCP chunking is
  nondeterministic — recv(S, N) is not), timeout and closed paths.
  """

  def go do
    {:ok, l} = :gen_tcp.listen(0, [:binary, {:active, false}, {:reuseaddr, true}])
    {:ok, port} = :inet.port(l)
    IO.puts(inspect(port > 0 and port < 65536))

    parent = self()

    server =
      spawn(fn ->
        {:ok, s} = :gen_tcp.accept(l)
        # echo fixed script: 5 bytes, then 6 bytes, then 4-byte quit
        {:ok, d1} = :gen_tcp.recv(s, 5)
        :ok = :gen_tcp.send(s, d1)
        {:ok, d2} = :gen_tcp.recv(s, 6)
        :ok = :gen_tcp.send(s, [d2, "!"])
        {:ok, "quit"} = :gen_tcp.recv(s, 4)
        :ok = :gen_tcp.close(s)
        send(parent, {:server_done, byte_size(d1) + byte_size(d2)})
      end)

    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])

    # peername/sockname agreement (ports never printed — only booleans)
    {:ok, {chost, cport}} = :inet.sockname(c)
    {:ok, {phost, pport}} = :inet.peername(c)
    IO.puts(inspect({chost, phost}))
    IO.puts(inspect(pport == port and cport != port))

    :ok = :gen_tcp.send(c, "hello")
    IO.puts(inspect(:gen_tcp.recv(c, 5)))

    :ok = :gen_tcp.send(c, "abcdef")
    IO.puts(inspect(:gen_tcp.recv(c, 3)))
    IO.puts(inspect(:gen_tcp.recv(c, 4)))

    # nothing pending: recv with a timeout
    IO.puts(inspect(:gen_tcp.recv(c, 1, 100)))

    :ok = :gen_tcp.send(c, "quit")

    receive do
      {:server_done, n} -> IO.puts(inspect({:server_done, n}))
    end

    # server closed its end: reads drain to closed
    IO.puts(inspect(:gen_tcp.recv(c, 1)))
    IO.puts(inspect(:gen_tcp.close(c)))

    # connect to a dead port fails fast
    {:ok, l2} = :gen_tcp.listen(0, [])
    {:ok, dead_port} = :inet.port(l2)
    :ok = :gen_tcp.close(l2)
    IO.puts(inspect(:gen_tcp.connect({127, 0, 0, 1}, dead_port, [], 1000)))

    # list mode
    {:ok, l3} = :gen_tcp.listen(0, [{:active, false}])
    {:ok, port3} = :inet.port(l3)

    spawn(fn ->
      {:ok, s} = :gen_tcp.accept(l3)
      :ok = :gen_tcp.send(s, "bytes")
      :ok = :gen_tcp.close(s)
    end)

    {:ok, c3} = :gen_tcp.connect(~c"localhost", port3, [{:active, false}])
    IO.puts(inspect(:gen_tcp.recv(c3, 5)))
    :ok = :gen_tcp.close(c3)
    :ok = :gen_tcp.close(l3)
    :ok = :gen_tcp.close(l)
    IO.puts(inspect(is_pid(server)))

    # active mode: {tcp, S, Data} / {tcp_closed, S} as real messages
    {:ok, l4} = :gen_tcp.listen(0, [:binary, {:active, false}])
    {:ok, port4} = :inet.port(l4)

    spawn(fn ->
      {:ok, s} = :gen_tcp.accept(l4)
      :ok = :gen_tcp.send(s, "one")
      # wait for the go-ahead so the two messages can't coalesce
      {:ok, "go"} = :gen_tcp.recv(s, 2)
      :ok = :gen_tcp.send(s, "two")
      {:ok, "go"} = :gen_tcp.recv(s, 2)
      :ok = :gen_tcp.close(s)
    end)

    {:ok, c4} = :gen_tcp.connect({127, 0, 0, 1}, port4, [:binary, {:active, :once}])

    receive do
      {:tcp, ^c4, data} -> IO.puts(inspect({:active_once, data}))
    end

    # active once consumed: no further tcp messages until re-armed
    receive do
      {:tcp, ^c4, _} -> IO.puts("unexpected")
    after
      100 -> IO.puts(inspect(:quiet))
    end

    :ok = :gen_tcp.send(c4, "go")
    :ok = :inet.setopts(c4, [{:active, true}])

    receive do
      {:tcp, ^c4, data} -> IO.puts(inspect({:active_true, data}))
    end

    :ok = :gen_tcp.send(c4, "go")

    receive do
      {:tcp_closed, ^c4} -> IO.puts(inspect(:tcp_closed))
    end

    :ok = :gen_tcp.close(c4)
    :ok = :gen_tcp.close(l4)

    # controlling_process: messages follow the new owner
    {:ok, l5} = :gen_tcp.listen(0, [:binary, {:active, false}])
    {:ok, port5} = :inet.port(l5)

    spawn(fn ->
      {:ok, s} = :gen_tcp.accept(l5)
      :ok = :gen_tcp.send(s, "for-child")
      :ok = :gen_tcp.close(s)
    end)

    {:ok, c5} = :gen_tcp.connect({127, 0, 0, 1}, port5, [:binary, {:active, false}])

    child =
      spawn(fn ->
        receive do
          {:tcp, s, data} ->
            send(parent, {:child_got, data})
            :gen_tcp.close(s)
        end
      end)

    :ok = :gen_tcp.controlling_process(c5, child)
    :ok = :inet.setopts(c5, [{:active, :once}])

    receive do
      {:child_got, data} -> IO.puts(inspect({:child_got, data}))
    end

    :ok = :gen_tcp.close(l5)

    :ok
  end
end
