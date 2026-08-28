defmodule Conf.Ord do
  @moduledoc """
  Conformance program: general term order, structural equality, and the
  tuple/list BIF pack. Every result printed must match BEAM's term order
  exactly (number < atom < ref < fun < pid < tuple < nil < list).
  """

  def go do
    # cross-type ordering
    :erlang.display(1 < :atom)
    :erlang.display(:atom < {1, 2})
    :erlang.display({1, 2} < [])
    :erlang.display([] < [1])
    :erlang.display(:erlang.self() < {:t})

    # atoms order by text
    :erlang.display(:abc < :abd)
    :erlang.display(:zebra > :apple)
    :erlang.display(sort([:pear, :apple, :zebra, :fig]))

    # deep structural equality and ordering
    :erlang.display({1, [2, 3], :a} == {1, [2, 3], :a})
    :erlang.display({1, [2, 3]} == {1, [2, 4]})
    :erlang.display([1, 2, 3] < [1, 2, 4])
    :erlang.display([1, 2] < [1, 2, 0])
    :erlang.display({1, 2} < {1, 2, 3})

    # mixed-type sort
    :erlang.display(sort([[3], :b, {2, 2}, 1, [], {1}, :a, 2]))

    # tuple BIFs
    t = {:a, :b, :c, :d}
    :erlang.display(:erlang.element(3, t))
    :erlang.display(:erlang.setelement(2, t, :x))
    :erlang.display(:erlang.tuple_size(t))

    # list BIFs
    l = [10, 20, 30]
    :erlang.display(:erlang.hd(l))
    :erlang.display(:erlang.tl(l))
    :erlang.display(:erlang.length(l))
    :erlang.display([1, 2] ++ [3, 4])
    :erlang.display([1, 2, 3, 2, 1] -- [2, 1])
    :erlang.display([] ++ [9])
    :erlang.display([1] ++ [])

    # misc
    :erlang.display(:erlang.min(3, :atom))
    :erlang.display(:erlang.max({1}, [1]))
    :erlang.display(:erlang.abs(-42))
    :erlang.display(:erlang.is_tuple(t))
    :erlang.display(:erlang.is_tuple(l))
    :erlang.display(:erlang.is_function(fn -> :x end))
    :erlang.display(:erlang.is_function(fn x -> x end, 1))
    :erlang.display(:erlang.is_function(fn x -> x end, 2))
    :erlang.display(:erlang.is_number(7))
    :erlang.display(:erlang.is_boolean(false))

    # badarg paths are catchable
    :erlang.display(
      try do
        :erlang.element(9, t)
      catch
        class, reason -> {:caught, class, reason}
      end
    )

    :erlang.display(
      try do
        :erlang.hd([])
      catch
        class, reason -> {:caught, class, reason}
      end
    )

    # sorted insertion keeps working across GC pressure
    big = churn_sort(200, [])
    :erlang.display(:erlang.length(big))
    :erlang.display(:erlang.hd(big))
  end

  # insertion sort via general compare
  defp sort([]), do: []
  defp sort([h | t]), do: insert(h, sort(t))

  defp insert(x, []), do: [x]

  defp insert(x, [h | t]) do
    if x <= h do
      [x, h | t]
    else
      [h | insert(x, t)]
    end
  end

  defp churn_sort(0, acc), do: acc

  defp churn_sort(n, acc) do
    churn_sort(n - 1, insert(rem(n * 7919, 1000), acc))
  end
end
