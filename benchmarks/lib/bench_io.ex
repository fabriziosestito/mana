defmodule Bench.Io do
  @moduledoc """
  I/O foundation scoreboard: file round-trips and TCP loopback echo.
  The tcp entry measures a full connect + send + exact recv + close cycle
  (everything inside the measured fun — no cross-process socket ownership).
  """

  @dir "/tmp/mana_bench_io_scratch"
  @kb :binary.copy(<<0xAB>>, 1024)
  @kb64 :binary.copy(<<0xCD>>, 64 * 1024)

  def run do
    File.rm_rf!(@dir)
    File.mkdir_p!(@dir)
    path = Path.join(@dir, "bench.bin")

    {:ok, l} = :gen_tcp.listen(0, [:binary, {:active, false}, {:reuseaddr, true}])
    {:ok, port} = :inet.port(l)
    spawn(fn -> echo_forever(l) end)

    Benchee.run(
      %{
        "file write+read 1KB" => fn ->
          File.write!(path, @kb)
          File.read!(path)
        end,
        "file write+read 64KB" => fn ->
          File.write!(path, @kb64)
          File.read!(path)
        end,
        "tcp connect+echo64+close" => fn ->
          {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
          :ok = :gen_tcp.send(c, :binary.copy(<<1>>, 64))
          {:ok, _} = :gen_tcp.recv(c, 64)
          :ok = :gen_tcp.close(c)
        end
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    File.rm_rf!(@dir)
    :ok
  end

  defp echo_forever(l) do
    case :gen_tcp.accept(l) do
      {:ok, s} ->
        spawn(fn -> echo_conn(s) end)
        echo_forever(l)

      {:error, _} ->
        :ok
    end
  end

  defp echo_conn(s) do
    case :gen_tcp.recv(s, 0) do
      {:ok, data} ->
        :ok = :gen_tcp.send(s, data)
        echo_conn(s)

      {:error, _} ->
        :gen_tcp.close(s)
    end
  end
end
