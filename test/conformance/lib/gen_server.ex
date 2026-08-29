defmodule Conf.GenServer do
  @moduledoc """
  Conformance program: real OTP gen_server compiled from the OTP beams —
  start_link, call, cast, handle_info, named registration, timeouts,
  stop semantics, monitors of servers, and an Agent on top.
  """
  use GenServer

  def go do
    # anonymous server: call/cast round-trips
    {:ok, pid} = GenServer.start_link(__MODULE__, 0)
    :erlang.display(GenServer.call(pid, :get))
    GenServer.cast(pid, {:add, 5})
    GenServer.cast(pid, {:add, 2})
    :erlang.display(GenServer.call(pid, :get))
    :erlang.display(GenServer.call(pid, {:mul, 10}))

    # plain messages arrive at handle_info
    send(pid, {:add_info, 3})
    :erlang.display(GenServer.call(pid, :get))

    # state threading under load (GC pressure through the server loop)
    Enum.each(1..200, fn i -> GenServer.cast(pid, {:add, i}) end)
    :erlang.display(GenServer.call(pid, :get))

    # reply from a spawned task via GenServer.reply
    :erlang.display(GenServer.call(pid, :deferred))

    # stop: terminate callback runs, then the server is gone
    :erlang.display(GenServer.stop(pid))
    :erlang.display(Process.alive?(pid))

    # named server
    {:ok, _} = GenServer.start_link(__MODULE__, 100, name: :conf_named)
    :erlang.display(GenServer.call(:conf_named, :get))
    :erlang.display(is_pid(Process.whereis(:conf_named)))
    :erlang.display(GenServer.stop(:conf_named))
    :erlang.display(Process.whereis(:conf_named))

    # call timeout: server that answers slowly
    {:ok, slow} = GenServer.start_link(__MODULE__, 0)

    :erlang.display(
      try do
        GenServer.call(slow, :slow, 50)
      catch
        :exit, {:timeout, _} -> :call_timed_out
      end
    )

    # monitor sees a server crash (reason preserved)
    {:ok, doomed} = GenServer.start(Conf.GenServer.Doomed, nil)
    ref = Process.monitor(doomed)
    GenServer.cast(doomed, :boom)

    receive do
      {:DOWN, ^ref, :process, _, reason} -> :erlang.display({:down, reason})
    end

    :erlang.display(Process.alive?(doomed))

    # Agent (gen_server underneath)
    {:ok, agent} = Agent.start_link(fn -> %{count: 0} end)
    Agent.update(agent, fn m -> Map.put(m, :count, m.count + 41) end)
    :erlang.display(Agent.get(agent, fn m -> m.count + 1 end))
    :erlang.display(Agent.stop(agent))

    :erlang.display(:gen_server_gate_done)
  end

  @impl true
  def init(n), do: {:ok, n}

  @impl true
  def handle_call(:get, _from, n), do: {:reply, n, n}
  def handle_call({:mul, x}, _from, n), do: {:reply, n * x, n}

  def handle_call(:deferred, from, n) do
    me = self()
    spawn(fn -> GenServer.reply(from, {:deferred_reply, n}) end)
    {:noreply, n}
  end

  def handle_call(:slow, _from, n) do
    receive do
    after
      200 -> :ok
    end

    {:reply, :too_late, n}
  end

  @impl true
  def handle_cast({:add, x}, n), do: {:noreply, n + x}

  @impl true
  def handle_info({:add_info, x}, n), do: {:noreply, n + x}

  @impl true
  def terminate(_reason, _n), do: :ok
end

defmodule Conf.GenServer.Doomed do
  use GenServer

  @impl true
  def init(_), do: {:ok, nil}

  @impl true
  def handle_cast(:boom, state), do: {:stop, :shutdown, state}
end
