defmodule Conf.Float do
  @moduledoc """
  Conformance program for floats. It checks literals, mixed arithmetic,
  `/`, :math, conversions, comparisons and sorting, display parity, and
  floats that survive GC and messages. The values avoid platform-dependent
  last-ulp noise.
  """

  def go do
    # literals and display parity
    :erlang.display(1.0)
    :erlang.display(-1.5)
    :erlang.display(0.1)
    :erlang.display(-0.0)
    :erlang.display(1.0e20)
    :erlang.display(1.0e-5)
    :erlang.display(123456.789)
    :erlang.display(3.0e-3)

    # arithmetic: int/int through /, mixed, float/float
    a = n(7)
    b = n(2)
    :erlang.display(a / b)
    :erlang.display(a + 0.5)
    :erlang.display(0.5 + a)
    :erlang.display(2.5 * b)
    :erlang.display(a - 0.25)
    :erlang.display(-(a / b))
    :erlang.display(abs(-2.5))
    :erlang.display(abs(n(-9)))
    :erlang.display(:erlang.float(a))
    :erlang.display(1.0 + 2)
    :erlang.display(10 / 4)
    :erlang.display(10 / 5)

    # conversions
    :erlang.display(trunc(3.7))
    :erlang.display(trunc(-3.7))
    :erlang.display(round(2.5))
    :erlang.display(round(-2.5))
    :erlang.display(floor(2.7))
    :erlang.display(floor(-2.7))
    :erlang.display(ceil(2.2))
    :erlang.display(ceil(-2.2))
    :erlang.display(:erlang.float_to_binary(2.5, [:short]))
    :erlang.display(:erlang.binary_to_float("3.25"))
    :erlang.display(Float.parse("6.75rest"))

    # :math
    :erlang.display(:math.sqrt(2.25))
    :erlang.display(:math.pow(2.0, 10))
    :erlang.display(:math.pi())
    :erlang.display(:math.log(1.0))
    :erlang.display(:math.exp(0.0))
    :erlang.display(:math.floor(2.5))

    # Comparisons and term order. == coerces, and =:= does not.
    :erlang.display(1 == 1.0)
    :erlang.display(1 === 1.0)
    :erlang.display(1.5 < 2)
    :erlang.display(2 < 1.5)
    :erlang.display(sort([2.5, 1, 3.5, 2, 0.5]))
    :erlang.display(:erlang.min(1, 1.0))
    :erlang.display(:erlang.max(2.0, 2))
    :erlang.display(is_float(1.0))
    :erlang.display(is_float(1))
    :erlang.display(is_number(1.5))

    # error paths
    :erlang.display(catcher(fn -> n(1) / n(0) end))
    :erlang.display(catcher(fn -> 1.0 / 0.0 end))
    :erlang.display(catcher(fn -> n(1) + :atom end))
    :erlang.display(catcher(fn -> div(3.0, 2) end))
    :erlang.display(catcher(fn -> :math.sqrt(-1.0) end))
    :erlang.display(catcher(fn -> :erlang.binary_to_float("nope") end))

    # floats in structures, under GC pressure, through messages
    m = %{pi: 3.14, e: 2.71}
    :erlang.display(m.pi + m.e)
    :erlang.display(churn(500, 0.0))
    me = self()
    :erlang.spawn(fn -> send(me, {:f, 1.25, [2.5, 3.75]}) end)

    receive do
      {:f, x, [y, z]} -> :erlang.display(x + y + z)
    end

    # Enum over floats: stdlib paths that were int-only before.
    :erlang.display(Enum.sum([1.5, 2.5, 3.0]))
    :erlang.display(Enum.max([1.5, 2, 0.5]))
    IO.puts("avg: #{Enum.sum(1..10) / 10}")
  end

  defp n(x), do: x

  defp sort([]), do: []
  defp sort([h | t]), do: insert(h, sort(t))
  defp insert(x, []), do: [x]

  defp insert(x, [h | t]) do
    if x <= h, do: [x, h | t], else: [h | insert(x, t)]
  end

  defp catcher(f) do
    try do
      f.()
    catch
      class, reason -> {:caught, class, reason}
    end
  end

  # Float accumulation across many minor GCs.
  defp churn(0, acc), do: Float.round(acc, 6)

  defp churn(i, acc) do
    l = [i * 1.5, i / 2, :math.sqrt(i * 1.0)]
    churn(i - 1, acc + Enum.sum(l) - i * 1.5 - i / 2 - :math.sqrt(i * 1.0) + 0.001)
  end
end
