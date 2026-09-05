defmodule Conf.Links do
  @moduledoc """
  Conformance program for links, monitors, and exit signals. It uses exit/1
  reasons, normal exits, and kill. Those are the paths whose reasons match
  BEAM exactly. Error-class reasons carry stacktraces that we do not build
  yet.
  """

  def go do
    # trap_exit: the exit/1 reason of a linked child arrives as a message.
    :erlang.process_flag(:trap_exit, true)
    pid = :erlang.spawn_link(fn -> exit(:custom_reason) end)

    receive do
      {:EXIT, ^pid, reason} -> :erlang.display({:trapped, reason})
    end

    # Normal exit of a linked child: a trapping process still sees it.
    pid2 = :erlang.spawn_link(fn -> :ok end)

    receive do
      {:EXIT, ^pid2, reason} -> :erlang.display({:normal_exit, reason})
    end

    # Monitor: DOWN arrives when the child completes.
    {pid3, ref3} = :erlang.spawn_monitor(fn -> :done end)

    receive do
      {:DOWN, ^ref3, :process, ^pid3, reason} -> :erlang.display({:down, reason})
    end

    # A monitor on a dead process: immediate noproc.
    dead = :erlang.spawn(fn -> :gone end)
    wait_dead()
    ref4 = :erlang.monitor(:process, dead)

    receive do
      {:DOWN, ^ref4, :process, ^dead, reason} -> :erlang.display({:noproc_down, reason})
    end

    # demonitor: no DOWN arrives.
    {_pid5, ref5} = :erlang.spawn_monitor(fn -> receive do: (:go -> :ok) end)
    :erlang.demonitor(ref5)

    receive do
      {:DOWN, ^ref5, _, _, _} -> :erlang.display(:should_not_happen)
    after
      50 -> :erlang.display(:demonitor_ok)
    end

    # exit/2 with kill: the target cannot trap it, and the reason becomes killed.
    {victim, vref} = :erlang.spawn_monitor(fn -> waiter() end)
    :erlang.exit(victim, :kill)

    receive do
      {:DOWN, ^vref, :process, ^victim, reason} -> :erlang.display({:killed, reason})
    end

    # Exit signal cascade: A links B. B dies abnormally. A does not trap, so
    # A dies too. We monitor A to observe it.
    me = self()

    a =
      :erlang.spawn(fn ->
        :erlang.process_flag(:trap_exit, false)
        b = :erlang.spawn_link(fn -> exit(:boom) end)
        send(me, {:b_is, b})
        waiter()
      end)

    aref = :erlang.monitor(:process, a)

    receive do
      {:b_is, _} -> :ok
    end

    receive do
      {:DOWN, ^aref, :process, ^a, reason} -> :erlang.display({:cascaded, reason})
    end

    # unlink: the death of the child no longer affects us. We stopped trapping.
    :erlang.process_flag(:trap_exit, false)
    safe = :erlang.spawn_link(fn -> receive do: (:die -> exit(:whatever)) end)
    :erlang.unlink(safe)
    send(safe, :die)

    receive do
    after
      50 -> :erlang.display(:unlink_survived)
    end
  end

  defp waiter do
    receive do
      :never -> :ok
    end
  end

  defp wait_dead do
    receive do
    after
      30 -> :ok
    end
  end
end
