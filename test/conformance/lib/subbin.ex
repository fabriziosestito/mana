defmodule Conf.Subbin do
  @moduledoc """
  Sub-binary views (zero-copy slices, threshold 64 bytes). The program
  checks equality, ordering, hashing, map keys, cross-process sends, ETF
  round-trips, and the slicing identities. It byte-diffs everything against
  BEAM, where none of this machinery exists (plain binaries). Any
  observable difference is a view leak.
  """

  def go do
    # A parent big enough that every interesting slice is > 64 bytes.
    parent = :binary.copy(<<"abcdefghij">>, 20)
    <<_skip::binary-size(10), rest::binary>> = parent
    :erlang.display(byte_size(rest))
    :erlang.display(rest == :binary.part(parent, 10, 190))

    # slices of slices (offset folding)
    <<_::binary-size(30), inner::binary>> = rest
    :erlang.display(byte_size(inner))
    :erlang.display(binary_part(inner, 0, 8))

    # Equality and ordering between viewed and copied representations.
    copy = :binary.copy(inner)
    :erlang.display(inner == copy)
    :erlang.display(inner === copy)
    :erlang.display({inner < parent, copy < parent})

    # Views as map keys resolve to the same entry as their copies.
    m = %{inner => :via_view}
    :erlang.display(Map.get(m, copy))
    m2 = Map.put(m, copy, :via_copy)
    :erlang.display(map_size(m2))

    # phash2 self-consistency. The values are mana-specific. The equality of
    # the two hashes is the oracle-independent fact, so it prints as a boolean.
    :erlang.display(:erlang.phash2(inner) == :erlang.phash2(copy))

    # split_binary and binary_part identities at the threshold boundary.
    {a, b} = :erlang.split_binary(parent, 100)
    :erlang.display({byte_size(a), byte_size(b)})
    :erlang.display(parent == <<a::binary, b::binary>>)
    small = binary_part(parent, 0, 8)
    :erlang.display(small)

    # Matching THROUGH a view: inline byte reads, utf8, and constant prefixes.
    <<h, h2, tail::binary>> = inner
    :erlang.display({h, h2, byte_size(tail)})
    <<"abcdef", _::binary>> = inner
    :erlang.display(:const_prefix_ok)

    # Views inside messages (the promotion path).
    me = self()
    spawn(fn -> send(me, {:v, inner}) end)

    got =
      receive do
        {:v, v} -> v
      end

    :erlang.display(got == copy)

    # The ETF round-trip of a view equals the round-trip of its copy.
    :erlang.display(:erlang.term_to_binary(inner) == :erlang.term_to_binary(copy))
    :erlang.display(:erlang.binary_to_term(:erlang.term_to_binary(inner)) == copy)

    # iolists and io emission through views
    :erlang.display(:erlang.iolist_size([inner, copy]))
    :erlang.display(:erlang.iolist_to_binary([small, "-", small]))

    # to_list and to_integer style conversions through a view
    digits_parent = :binary.copy(<<"1234567890">>, 10)
    <<_::binary-size(20), dig_view::binary>> = digits_parent
    :erlang.display(:erlang.binary_to_integer(binary_part(dig_view, 0, 6)))
    :erlang.display(length(:erlang.binary_to_list(dig_view)))

    # binary:copy de-pins. The result must be a plain equal binary.
    depinned = :binary.copy(inner)
    :erlang.display(depinned == inner)

    # GC churn with live views: force collections while views are live.
    :erlang.display(churn(inner, 200, 0))

    :erlang.display(:done)
    :ok
  end

  # Allocates heavily and re-derives facts from a live view on every step.
  # A parent-forwarding bug shows up here as wrong bytes or a crash.
  defp churn(_view, 0, acc), do: acc

  defp churn(view, n, acc) do
    garbage = :binary.copy(<<n>>, 1000)
    <<b, _::binary>> = view
    churn(view, n - 1, acc + b + byte_size(garbage) - 1000)
  end
end
