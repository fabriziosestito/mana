defmodule Conf.CounterHttp do
  @moduledoc """
  Minimal probe: boot the app and GET /counter over gen_tcp, printing only
  the status and whether the LiveView dead-render markers are present. Used
  to isolate whether a smaller reachable-module set breaks LiveView
  serving (vs the richer Conf.Ws).
  """

  def go do
    port = Conf.WsClient.boot()
    {status, _headers, body} = Conf.WsClient.get(port, "/counter")
    IO.puts(status)
    IO.puts(inspect(String.contains?(body, "Count:")))
    IO.puts(inspect(String.contains?(body, "data-phx-main")))
    IO.puts(inspect(:done))
    :ok
  end
end
