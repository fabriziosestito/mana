defmodule Conf.Maps do
  @moduledoc """
  Conformance program for flatmap construction, update, pattern matching,
  the maps BIF pack, term order with maps, and maps as keys.

  The flatmap key order of BEAM is an implementation detail, not term
  order. Multi-key maps therefore never display directly. They go through
  `dump/1`, a deterministic sorted key/value listing. Empty and single-pair
  maps display fine as they are.
  """

  def go do
    m = %{b: 2, a: 1, c: 3}
    dump(m)
    :erlang.display(%{})
    :erlang.display(%{solo: 1})
    dump(%{1 => :one, :atom => :two, {1, 2} => :three, [] => :four})

    # Duplicate keys in a literal: the last one wins.
    :erlang.display(%{k(:a) => 1, k(:a) => 2})

    # BIF pack
    :erlang.display(:maps.get(:b, m))
    :erlang.display(:maps.get(:missing, m, :fallback))
    :erlang.display(:maps.find(:a, m))
    :erlang.display(:maps.find(:nope, m))
    :erlang.display(:maps.is_key(:c, m))
    :erlang.display(:maps.is_key(:z, m))
    dump(:maps.put(:d, 4, m))
    dump(:maps.put(:a, 99, m))
    dump(:maps.remove(:b, m))
    dump(:maps.remove(:absent, m))
    :erlang.display(:maps.size(m))
    dump(:maps.from_list([{:x, 1}, {:y, 2}, {:x, 3}]))
    dump(:maps.merge(m, %{b: 20, d: 40}))

    # erlang-module surface
    :erlang.display(:erlang.map_size(m))
    :erlang.display(:erlang.is_map(m))
    :erlang.display(:erlang.is_map([]))
    :erlang.display(:erlang.is_map_key(:a, m))
    :erlang.display(:erlang.map_get(:c, m))

    # update (exact) syntax
    dump(%{m | b: 22})

    # pattern matching
    %{a: av, c: cv} = m
    :erlang.display({av, cv})
    :erlang.display(classify(%{tag: :circle, r: 5}))
    :erlang.display(classify(%{tag: :rect, w: 2, h: 3}))
    :erlang.display(classify(%{other: 1}))
    :erlang.display(classify(:not_a_map))

    # maps in guards
    :erlang.display(guarded(%{size: 10}))
    :erlang.display(guarded(%{size: 1}))
    :erlang.display(guarded(%{}))

    # Structural equality and term order. The canonical form is order-insensitive.
    :erlang.display(%{a: 1, b: 2} == %{b: 2, a: 1})
    :erlang.display(%{a: 1} == %{a: 1, b: 2})
    :erlang.display(%{a: 1} < %{a: 1, b: 2})
    :erlang.display(%{a: 1} < %{a: 2})
    :erlang.display({:t} < %{a: 1})
    :erlang.display(%{} < [])
    :erlang.display(:atom < %{})

    # maps as keys and values, nested
    nested = %{%{k: 1} => :map_key, outer: %{inner: %{deep: :yes}}}
    :erlang.display(:maps.get(%{k: 1}, nested))
    %{outer: %{inner: %{deep: d}}} = nested
    :erlang.display(d)

    # A struct-shaped map, which is what %SomeStruct{} compiles to.
    s = %{__struct__: FakeStruct, field: 1}
    :erlang.display(:maps.get(:__struct__, s))

    # Error paths are catchable and match the BEAM reasons.
    :erlang.display(catcher(fn -> :maps.get(:nope, m) end))
    :erlang.display(catcher(fn -> :maps.get(:k, :not_a_map) end))
    :erlang.display(catcher(fn -> :maps.put(:k, :v, [1]) end))
    :erlang.display(catcher(fn -> %{:not_a_map | a: 1} end))
    :erlang.display(catcher(fn -> %{%{a: 1} | b: 2} end))
    :erlang.display(catcher(fn -> :erlang.map_get(:x, %{}) end))

    # GC pressure: build and tear down maps across collections, then cross-check the sum.
    :erlang.display(churn(500, %{}, 0))

    # Maps that travel through messages. The promotion path scans the map kind.
    me = self()
    :erlang.spawn(fn -> send(me, %{from: :child, data: [1, 2, 3]}) end)

    receive do
      %{from: who, data: l} -> :erlang.display({who, :erlang.length(l)})
    end
  end

  # A deterministic view of a map: sorted key/value pairs.
  defp dump(m), do: :erlang.display({:map, sort(:maps.to_list(m))})

  defp sort([]), do: []
  defp sort([h | t]), do: insert(h, sort(t))
  defp insert(x, []), do: [x]

  defp insert(x, [h | t]) do
    if x <= h, do: [x, h | t], else: [h | insert(x, t)]
  end

  defp k(x), do: x

  defp classify(%{tag: :circle, r: r}), do: {:circle, r}
  defp classify(%{tag: :rect, w: w, h: h}), do: {:rect, w * h}
  defp classify(m) when is_map(m), do: :unknown_shape
  defp classify(_), do: :not_a_map

  defp guarded(m) when is_map_key(m, :size) and map_size(m) > 0 do
    if :maps.get(:size, m) > 5, do: :big, else: :small
  end

  defp guarded(m) when is_map(m), do: :empty

  defp catcher(f) do
    try do
      f.()
    catch
      class, reason -> {:caught, class, reason}
    end
  end

  # Rotates keys through a small map under allocation pressure.
  defp churn(0, m, acc), do: {:erlang.map_size(m), acc}

  defp churn(n, m, acc) do
    key = rem(n, 16)
    m2 = :maps.put(key, [n, n * 2, {n}], m)
    v = :maps.get(key, m2)
    m3 = if rem(n, 5) == 0, do: :maps.remove(rem(n + 3, 16), m2), else: m2
    churn(n - 1, m3, acc + :erlang.hd(v))
  end
end
