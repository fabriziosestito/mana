defmodule Bench.Classic do
  @moduledoc """
  The scoreboard as a benchee suite. The identical module runs on BEAM and
  on mana. Memory and reduction collection stays off, because tracing is
  BEAM-internal.
  """

  def run do
    Benchee.run(
      %{
        "fib 25" => fn -> fib(25) end,
        "list churn 5k" => fn -> churn(5_000) end,
        "map ops 1k" => fn -> map_ops(1_000) end,
        "binary build+match 1k" => fn -> bin_ops(1_000) end
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end

  defp fib(0), do: 0
  defp fib(1), do: 1
  defp fib(n), do: fib(n - 1) + fib(n - 2)

  defp churn(n) do
    1..n |> Enum.to_list() |> Enum.reverse() |> Enum.sum()
  end

  defp map_ops(n) do
    Enum.reduce(1..n, %{}, fn i, acc -> Map.put(acc, rem(i, 64), i) end)
    |> map_size()
  end

  defp bin_ops(n) do
    b = Enum.reduce(1..n, <<>>, fn i, acc -> <<acc::binary, rem(i, 256)>> end)
    <<_::8, rest::binary>> = b
    byte_size(rest)
  end
end
