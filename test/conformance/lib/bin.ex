defmodule Conf.Bin do
  @moduledoc """
  Conformance program for byte-aligned binaries. It checks construction,
  pattern matching (heads, nesting, fixed-size and rest segments,
  endianness, signedness), the binary BIF pack, term order, and GC and
  message traffic. binary_to_atom only runs with atoms that exist in the
  program. The closed world gives it binary_to_existing_atom semantics.
  """

  def go do
    # Literals and display heuristics.
    :erlang.display("hello")
    :erlang.display(<<>>)
    :erlang.display(<<1, 2, 3>>)
    :erlang.display(<<200, 255, 0>>)
    :erlang.display("say \"hi\" \\ there")
    :erlang.display("héllo")
    :erlang.display(<<9, 10, 13>>)

    # construction: sizes, endianness, splices, computed values
    n = compute(258)
    :erlang.display(<<n::16>>)
    :erlang.display(<<n::16-little>>)
    :erlang.display(<<n::32>>)
    :erlang.display(<<n::64>>)
    :erlang.display(<<7>> <> "abc" <> <<n::8>>)
    b = "abc"
    :erlang.display(<<b::binary, 0, b::binary>>)
    :erlang.display(byte_size(<<1, b::binary, n::32>>))

    # patterns
    <<h::8, rest::binary>> = "hello"
    :erlang.display({h, rest})
    <<a::binary-size(2), c::binary-size(1), r::binary>> = "abcdef"
    :erlang.display({a, c, r})
    <<x::16, y::16-little, z::8-signed>> = <<1, 2, 3, 4, 255>>
    :erlang.display({x, y, z})
    :erlang.display(parse("MAGIC-payload"))
    :erlang.display(parse("WRONG-payload"))
    :erlang.display(parse("MAG"))
    :erlang.display(exact(<<1, 2>>))
    :erlang.display(exact(<<1, 2, 3>>))

    # nested patterns
    {:frame, <<len::16, body::binary>>} = {:frame, <<0, 2, "ok">>}
    :erlang.display({len, body})
    [<<f::8, fr::binary>> | _] = ["xyz"]
    :erlang.display({f, fr})
    %{data: <<d::8, dr::binary>>} = %{data: <<42, "tail">>}
    :erlang.display({d, dr})

    # case dispatch on binary shapes
    :erlang.display(kind(<<0, 1, 2>>))
    :erlang.display(kind(<<1, "rest">>))
    :erlang.display(kind(<<9>>))
    :erlang.display(kind(:other))

    # BIF pack
    :erlang.display(byte_size("hello"))
    :erlang.display(bit_size("hi"))
    :erlang.display(:erlang.binary_part("hello", 1, 3))
    :erlang.display(:erlang.binary_part("hello", 5, -2))
    :erlang.display(:erlang.binary_to_list("abc"))
    :erlang.display(:erlang.list_to_binary([104, 105]))
    :erlang.display(:erlang.list_to_binary([[104, "i"], <<33>>, []]))
    :erlang.display(:erlang.iolist_to_binary(["a", [<<98>>, [99]], "d"]))
    :erlang.display(:erlang.integer_to_binary(-1234))
    :erlang.display(:erlang.integer_to_binary(0))
    :erlang.display(:erlang.atom_to_binary(:hello_world))
    :erlang.display(:erlang.binary_to_atom(<<"hello_world">>))
    :erlang.display(:erlang.binary_to_existing_atom("kind"))
    :erlang.display(:erlang.is_binary("x"))
    :erlang.display(:erlang.is_binary([1]))
    :erlang.display(:erlang.is_bitstring(<<>>))

    # term order and equality
    :erlang.display(<<1, 2>> < <<1, 2, 3>>)
    :erlang.display(<<2>> > <<1, 9, 9>>)
    :erlang.display("abc" == "abc")
    :erlang.display("abc" == "abd")
    :erlang.display({:x} < "bin")
    :erlang.display([1] < "bin")
    :erlang.display(sort(["pear", "apple", <<3>>, "fig", <<1, 200>>]))
    m = %{"key" => 1, <<0>> => 2}
    :erlang.display(:maps.get("key", m))
    :erlang.display(:maps.get(<<0>>, m))

    # error paths
    :erlang.display(catcher(fn -> byte_size(:not_a_bin) end))
    :erlang.display(catcher(fn -> :erlang.binary_part("abc", 2, 5) end))
    :erlang.display(catcher(fn -> :erlang.list_to_binary([300]) end))
    :erlang.display(catcher(fn -> :erlang.binary_to_existing_atom("no_such_atom_zzz") end))
    :erlang.display(catcher(fn -> <<opaque()::8>> end))

    # GC pressure: build and slice binaries across collections.
    :erlang.display(churn(300, 0))

    # Binaries through messages (the promotion path).
    me = self()
    :erlang.spawn(fn -> send(me, {:bin, <<1, 2, 3, "from child">>}) end)

    receive do
      {:bin, <<1, t::8, _::binary>> = whole} -> :erlang.display({t, byte_size(whole)})
    end
  end

  defp compute(x), do: x + 0

  defp opaque, do: :atom

  defp parse(<<"MAGIC-", payload::binary>>), do: {:ok, payload}
  defp parse(_), do: :error

  defp exact(<<_::8, _::8>>), do: :two
  defp exact(_), do: :not_two

  defp kind(<<0, _::binary>>), do: :zero_prefixed
  defp kind(<<_::8, rest::binary>>) when byte_size(rest) > 0, do: {:framed, byte_size(rest)}
  defp kind(b) when is_binary(b), do: :single
  defp kind(_), do: :not_binary

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

  defp churn(0, acc), do: acc

  defp churn(n, acc) do
    b = <<n::32, "some payload data", n::16-little>>
    <<v::32, _::binary-size(17), w::16-little>> = b
    l = :erlang.binary_to_list(:erlang.binary_part(b, 0, 4))
    churn(n - 1, acc + v + w + :erlang.length(l) - n - n)
  end
end
