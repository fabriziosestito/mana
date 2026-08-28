defmodule Conf.Procs do
  @moduledoc """
  Conformance program: processes — spawn, zero-copy send, selective
  receive (out-of-order matching), fan-out/collect, timeouts, message
  data surviving collections, process crash isolation.
  """

  def go do
    # ping-pong, several rounds through two processes
    me = self()
    pong = :erlang.spawn(fn -> pong_loop() end)
    :erlang.display(ping(pong, me, 5, 0))

    # selective receive: take messages out of arrival order
    send(self(), {:b, 2})
    send(self(), {:a, 1})
    send(self(), {:c, 3})

    a =
      receive do
        {:a, x} -> x
      end

    b =
      receive do
        {:b, x} -> x
      end

    c =
      receive do
        {:c, x} -> x
      end

    :erlang.display({:ordered, a, b, c})

    # fan-out: workers compute and reply; collect in worker order
    pids = fan_out(me, 10, [])
    :erlang.display(collect(pids, 0))

    # messages carrying structure, with allocation pressure forcing GC
    # between send and receive
    :erlang.spawn(fn -> send(me, {:payload, range(1, 100)}) end)
    _junk = churn(50, [])

    receive do
      {:payload, l} -> :erlang.display(sum(l, 0))
    end

    # timeout fires when nothing arrives; 0 polls
    receive do
      :never -> :erlang.display(:impossible)
    after
      50 -> :erlang.display(:timed_out)
    end

    receive do
      :never -> :erlang.display(:impossible)
    after
      0 -> :erlang.display(:empty_poll)
    end
  end

  defp ping(_pong, _me, 0, acc), do: {:pinged, acc}

  defp ping(pong, me, n, acc) do
    send(pong, {:ping, me, n})

    receive do
      {:pong, v} -> ping(pong, me, n - 1, acc + v)
    end
  end

  defp pong_loop do
    receive do
      {:ping, from, n} ->
        send(from, {:pong, n * 2})
        pong_loop()
    end
  end

  defp fan_out(_me, 0, acc), do: acc

  defp fan_out(me, n, acc) do
    pid = :erlang.spawn(fn -> send(me, {:result, n, n * n}) end)
    fan_out(me, n - 1, [{pid, n} | acc])
  end

  defp collect([], acc), do: {:sum_of_squares, acc}

  defp collect([{_pid, n} | rest], acc) do
    receive do
      {:result, ^n, sq} -> collect(rest, acc + sq)
    end
  end

  defp range(n, n), do: [n]
  defp range(i, n), do: [i | range(i + 1, n)]

  defp sum([], acc), do: acc
  defp sum([h | t], acc), do: sum(t, acc + h)

  defp churn(0, acc), do: acc
  defp churn(n, _acc), do: churn(n - 1, range(1, 200))
end
