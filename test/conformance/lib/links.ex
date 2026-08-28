defmodule Conf.Links do
  @moduledoc """
  Conformance program: links, monitors, exit signals. Uses exit/1 reasons,
  normal exits, and kill — the paths whose reasons match BEAM exactly
  (error-class reasons carry stacktraces we don't build yet).
  """

  def go do
    # trap_exit: linked child's exit/1 reason arrives as a message
    :erlang.process_flag(:trap_exit, true)
    pid = :erlang.spawn_link(fn -> exit(:custom_reason) end)

    receive do
      {:EXIT, ^pid, reason} -> :erlang.display({:trapped, reason})
    end

    # normal exit of a linked child: trapping still sees it
    pid2 = :erlang.spawn_link(fn -> :ok end)

    receive do
      {:EXIT, ^pid2, reason} -> :erlang.display({:normal_exit, reason})
    end

    # monitor: DOWN on child completion
    {pid3, ref3} = :erlang.spawn_monitor(fn -> :done end)

    receive do
      {:DOWN, ^ref3, :process, ^pid3, reason} -> :erlang.display({:down, reason})
    end

    # monitoring a dead process: immediate noproc
    dead = :erlang.spawn(fn -> :gone end)
    wait_dead()
    ref4 = :erlang.monitor(:process, dead)

    receive do
      {:DOWN, ^ref4, :process, ^dead, reason} -> :erlang.display({:noproc_down, reason})
    end

    # demonitor: no DOWN arrives
    {_pid5, ref5} = :erlang.spawn_monitor(fn -> receive do: (:go -> :ok) end)
    :erlang.demonitor(ref5)

    receive do
      {:DOWN, ^ref5, _, _, _} -> :erlang.display(:should_not_happen)
    after
      50 -> :erlang.display(:demonitor_ok)
    end

    # exit/2 kill: untrappable in the target, reason becomes killed
    {victim, vref} = :erlang.spawn_monitor(fn -> waiter() end)
    :erlang.exit(victim, :kill)

    receive do
      {:DOWN, ^vref, :process, ^victim, reason} -> :erlang.display({:killed, reason})
    end

    # exit signal cascade: A links B; B dies abnormally; A (not trapping)
    # dies too; we monitor A to observe it
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

    # unlink: child death no longer affects us (we stopped trapping)
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
