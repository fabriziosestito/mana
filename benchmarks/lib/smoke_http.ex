defmodule Smoke.Http do
  @moduledoc "Manual curl smoke: serve on a fixed port until killed."
  def run do
    :logger.remove_handler(:default)

    {:ok, _} =
      Bandit.start_link(
        plug: Bench.Http.HelloPlug,
        scheme: :http,
        port: 18080,
        startup_log: false,
        http_options: [compress: false],
        http_2_options: [enabled: false]
      )

    IO.puts("listening on 18080")
    Process.sleep(:infinity)
  end
end
