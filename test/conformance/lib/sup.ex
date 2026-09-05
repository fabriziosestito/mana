defmodule Conf.Sup.Worker do
  use GenServer

  def start_link(arg), do: GenServer.start_link(__MODULE__, arg, name: elem(arg, 0))
  def init({_name, parent}), do: {:ok, parent}

  def handle_call(:ping, _from, parent), do: {:reply, :pong, parent}
  def handle_call(:boom, _from, _parent), do: raise("boom")
end

defmodule Conf.Sup do
  @moduledoc """
  Conformance program for supervision. It checks Supervisor restart on
  crash, DynamicSupervisor.start_child, Task.start_link, and Task.async/await.
  """

  def go do
    # BEAM prints crash reports to stdout through the default logger
    # handler. Remove it so that both runtimes stay silent. Our :logger cut
    # is a no-op.
    :logger.remove_handler(:default)
    parent = self()

    children = [
      %{
        id: :w1,
        start: {Conf.Sup.Worker, :start_link, [{:w1, parent}]},
        restart: :permanent
      }
    ]

    {:ok, sup} = Supervisor.start_link(children, strategy: :one_for_one)
    IO.puts(inspect(GenServer.call(:w1, :ping)))
    IO.puts(inspect(Enum.sort(Map.to_list(Supervisor.count_children(sup)))))

    # Crash the worker. The supervisor restarts it under the same name.
    pid1 = Process.whereis(:w1)

    try do
      GenServer.call(:w1, :boom)
    catch
      :exit, _ -> IO.puts(inspect(:call_exited))
    end

    wait_restart(:w1, pid1, 200)
    IO.puts(inspect(GenServer.call(:w1, :ping)))
    IO.puts(inspect(Process.whereis(:w1) != pid1))

    # DynamicSupervisor
    {:ok, dyn} = DynamicSupervisor.start_link(strategy: :one_for_one)

    {:ok, w2} =
      DynamicSupervisor.start_child(dyn, %{
        id: :w2,
        start: {Conf.Sup.Worker, :start_link, [{:w2, parent}]},
        restart: :temporary
      })

    IO.puts(inspect(GenServer.call(w2, :ping)))
    IO.puts(inspect(Enum.sort(Map.to_list(DynamicSupervisor.count_children(dyn)))))
    :ok = DynamicSupervisor.terminate_child(dyn, w2)
    IO.puts(inspect(Enum.sort(Map.to_list(DynamicSupervisor.count_children(dyn)))))

    # Task
    {:ok, _t} = Task.start_link(fn -> send(parent, :task_ran) end)

    receive do
      :task_ran -> IO.puts(inspect(:task_ran))
    end

    task = Task.async(fn -> 6 * 7 end)
    IO.puts(inspect(Task.await(task)))

    IO.puts(inspect(is_pid(sup) and is_pid(dyn)))
    :ok
  end

  defp wait_restart(name, old, tries) do
    case Process.whereis(name) do
      pid when is_pid(pid) and pid != old ->
        :ok

      _ when tries > 0 ->
        Process.sleep(5)
        wait_restart(name, old, tries - 1)

      _ ->
        :timeout
    end
  end
end
