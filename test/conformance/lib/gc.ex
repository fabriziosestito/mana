defmodule Conf.Gc do
  @moduledoc """
  Conformance program: garbage collector stress. The initial heap is ~8KB,
  so these loops force many copying collections; any root left in a
  register across a GC point, any bad forwarding, or any mis-scanned object
  shows up as wrong output or a crash.
  """

  def go do
    # long list construction + traversal (cons churn)
    l = range(1, 20_000)
    :erlang.display(sum(l, 0))
    :erlang.display(len(l, 0))

    # reversal allocates a second copy while the first is live
    r = rev(l, [])
    :erlang.display(hd_of(r))
    :erlang.display(sum(r, 0))

    # tuple churn: build and immediately drop tuples in a loop
    :erlang.display(tuple_churn(10_000, 0))

    # closures surviving collections: capture, allocate a lot, then call
    k = 42
    add_k = fn x -> x + k end
    junk = range(1, 5_000)
    :erlang.display(add_k.(sum(junk, 0)))

    # deep structure copied through several collections
    t = build_tree(10)
    :erlang.display(tree_sum(t))
  end

  defp range(n, n), do: [n]
  defp range(i, n), do: [i | range(i + 1, n)]

  defp sum([], acc), do: acc
  defp sum([h | t], acc), do: sum(t, acc + h)

  defp len([], acc), do: acc
  defp len([_ | t], acc), do: len(t, acc + 1)

  defp rev([], acc), do: acc
  defp rev([h | t], acc), do: rev(t, [h | acc])

  defp hd_of([h | _]), do: h

  defp tuple_churn(0, acc), do: acc

  defp tuple_churn(n, acc) do
    {a, b} = {n, acc}
    tuple_churn(a - 1, b + a)
  end

  defp build_tree(0), do: {:leaf, 1}
  defp build_tree(n), do: {:node, build_tree(n - 1), build_tree(n - 1)}

  defp tree_sum({:leaf, v}), do: v
  defp tree_sum({:node, l, r}), do: tree_sum(l) + tree_sum(r)
end
