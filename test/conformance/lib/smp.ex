defmodule Conf.Smp do
  @moduledoc """
  Conformance program for SMP stress. Many processes exchange allocating
  payloads across schedulers. The traffic forces minor collections
  (promotion churn) and old-space growth (majors). The output is
  deterministic for any scheduler count.
  """

  def go do
    me = self()

    # 32 workers, 20 rounds each. Every round builds a fresh list (nursery
    # churn) and sends it for summation. The reply crosses back.
    workers = spawn_workers(me, 32, [])
    :erlang.display(drive(workers, 20, 0))

    # Chain: a token passes through 100 processes, and each adds its index.
    :erlang.display(chain(me, 100))

    # Burst: everyone sends at once. Collect deterministically by index.
    burst = spawn_burst(me, 64, [])
    :erlang.display(collect_burst(burst, 0))
  end

  defp spawn_workers(_me, 0, acc), do: acc

  defp spawn_workers(me, n, acc) do
    pid = :erlang.spawn(fn -> worker(me) end)
    spawn_workers(me, n - 1, [{n, pid} | acc])
  end

  defp worker(boss) do
    receive do
      {:job, k, payload} ->
        send(boss, {:done, k, sum(payload, 0)})
        worker(boss)

      :stop ->
        :ok
    end
  end

  defp drive(workers, 0, acc) do
    stop_all(workers)
    {:total, acc}
  end

  defp drive(workers, round, acc) do
    sent = send_jobs(workers, round, 0)
    got = collect_jobs(workers, round, 0)
    drive(workers, round - 1, acc + got - sent + sent)
  end

  defp send_jobs([], _round, n), do: n

  defp send_jobs([{k, pid} | rest], round, n) do
    send(pid, {:job, k, range(1, 50 + k + round)})
    send_jobs(rest, round, n + 1)
  end

  defp collect_jobs([], _round, acc), do: acc

  defp collect_jobs([{k, _pid} | rest], round, acc) do
    receive do
      {:done, ^k, s} -> collect_jobs(rest, round, acc + s)
    end
  end

  defp stop_all([]), do: :ok

  defp stop_all([{_k, pid} | rest]) do
    send(pid, :stop)
    stop_all(rest)
  end

  defp chain(me, n) do
    last = build_chain(me, n)
    send(last, {:token, 0})

    receive do
      {:token, v} -> {:chained, v}
    end
  end

  defp build_chain(down, 0), do: down

  defp build_chain(down, n) do
    next =
      :erlang.spawn(fn ->
        receive do
          {:token, v} -> send(down, {:token, v + n})
        end
      end)

    build_chain(next, n - 1)
  end

  defp spawn_burst(_me, 0, acc), do: acc

  defp spawn_burst(me, n, acc) do
    :erlang.spawn(fn -> send(me, {:burst, n, n * 3}) end)
    spawn_burst(me, n - 1, [n | acc])
  end

  defp collect_burst([], acc), do: {:burst_total, acc}

  defp collect_burst([n | rest], acc) do
    receive do
      {:burst, ^n, v} -> collect_burst(rest, acc + v)
    end
  end

  defp range(n, n), do: [n]
  defp range(i, n), do: [i | range(i + 1, n)]

  defp sum([], acc), do: acc
  defp sum([h | t], acc), do: sum(t, acc + h)
end
