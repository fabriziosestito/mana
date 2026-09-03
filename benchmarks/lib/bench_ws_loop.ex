defmodule Bench.WsLoop do
  @moduledoc """
  Profiling vehicle for the LiveView event round-trip: boot, join once, then a
  plain tight loop of phx-click round-trips with no benchee machinery, so
  callgrind attributes cost to the server path (transport + channel + diff +
  serializer). `Bench.Ws` (benchee) stays the official scoreboard.

  Note the client side (Jason encode/decode + frame codec in this process)
  shows up in the profile too — read the attribution per module.
  """

  @iters 5_000

  def run do
    port = Bench.Ws.boot()
    IO.puts("Bench.WsLoop: #{Bench.Env.tag()}")
    {sock, topic} = Bench.Ws.join(port)

    {us, :ok} = :timer.tc(fn -> loop(@iters, sock, topic) end)
    :io.format("event roundtrip: ~.1f us/iter over ~p iters~n", [us / @iters, @iters])
    :gen_tcp.close(sock)
    :ok
  end

  defp loop(0, _sock, _topic), do: :ok

  defp loop(n, sock, topic) do
    :ok = Bench.Ws.click(sock, topic)
    loop(n - 1, sock, topic)
  end
end
