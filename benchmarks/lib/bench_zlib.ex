defmodule Bench.Zlib do
  @moduledoc """
  DEFLATE throughput against warm BEAM: gzip of a representative HTML body,
  and a streaming raw deflate and inflate roundtrip (the permessage-deflate
  shape). The compressed bytes differ from BEAM, because miniz_oxide is not
  zlib. This measures wall time on our workload. It is the second
  dependency-policy gate.
  """

  @html String.duplicate(
          """
          <div class="card"><h1>Count: <span id="count">0</span></h1>
          <button phx-click="inc">+1</button><p>the quick brown fox</p></div>
          """,
          40
        )

  def run do
    Benchee.run(
      %{
        "gzip 4KB html" => fn -> :zlib.gzip(@html) end,
        "gunzip 4KB html" => fn -> :zlib.gunzip(:zlib.gzip(@html)) end,
        "raw deflate+inflate roundtrip" => fn -> roundtrip(@html) end
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end

  defp roundtrip(data) do
    zd = :zlib.open()
    :zlib.deflateInit(zd, :default, :deflated, -15, 8, :default)
    comp = IO.iodata_to_binary(:zlib.deflate(zd, data, :sync))
    :zlib.close(zd)

    zi = :zlib.open()
    :zlib.inflateInit(zi, -15)
    out = IO.iodata_to_binary(drain(zi, comp))
    :zlib.close(zi)
    out
  end

  defp drain(z, data) do
    case :zlib.safeInflate(z, data) do
      {:continue, out} -> [out | drain(z, [])]
      {:finished, out} -> [out]
    end
  end
end
