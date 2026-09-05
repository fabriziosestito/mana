defmodule Conf.Apply do
  @moduledoc """
  Conformance program for dynamic dispatch. It checks apply/3 on computed
  module and function atoms (protocol-shaped dispatch), apply/2 on funs,
  undef on unknown targets, and dispatch under GC pressure.
  """

  def go do
    # apply/3 with computed module/function atoms
    :erlang.display(:erlang.apply(Conf.ApplyHelper, :double, [21]))
    m = pick(:helper)
    f = pick(:fun)
    :erlang.display(:erlang.apply(m, f, [5]))
    :erlang.display(:erlang.apply(m, :pair, [1, 2]))
    :erlang.display(:erlang.apply(m, :zero, []))

    # The dynamic call syntax compiles to apply/3.
    :erlang.display(m.double(100))

    # dispatch table driven by data (protocol shape)
    :erlang.display(run_all([{m, :double, [2]}, {m, :pair, [:a, :b]}, {m, :zero, []}]))

    # apply/2 on closures
    add = fn a, b -> a + b end
    :erlang.display(:erlang.apply(add, [3, 4]))
    :erlang.display(:erlang.apply(fn -> :nullary end, []))
    cap = 10
    :erlang.display(:erlang.apply(fn x -> x + cap end, [5]))

    # undef and badarg are catchable.
    :erlang.display(catcher(fn -> :erlang.apply(m, :no_such_fun, [1]) end))
    :erlang.display(catcher(fn -> :erlang.apply(pick(:missing), :f, []) end))
    :erlang.display(catcher(fn -> :erlang.apply(m, :double, [1, 2]) end))

    # Atoms made from binaries drive dispatch (closed-world identity).
    f2 = :erlang.binary_to_atom(<<"double">>)
    :erlang.display(:erlang.apply(m, f2, [50]))

    # dispatch in a loop under allocation pressure
    :erlang.display(churn(300, 0))
  end

  defp pick(:helper), do: Conf.ApplyHelper
  defp pick(:missing), do: :no_such_module
  defp pick(:fun), do: :double

  defp run_all([]), do: []
  defp run_all([{m, f, a} | t]), do: [:erlang.apply(m, f, a) | run_all(t)]

  defp catcher(g) do
    try do
      g.()
    catch
      class, reason -> {:caught, class, reason}
    end
  end

  defp churn(0, acc), do: acc

  defp churn(n, acc) do
    f = if rem(n, 2) == 0, do: :double, else: :succ
    v = :erlang.apply(Conf.ApplyHelper, f, [n])
    churn(n - 1, acc + v - n)
  end
end

defmodule Conf.ApplyHelper do
  def double(x), do: x * 2
  def succ(x), do: x + 1
  def pair(a, b), do: {a, b}
  def zero, do: :zero_result
end
