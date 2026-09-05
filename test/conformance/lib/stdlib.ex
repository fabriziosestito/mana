defmodule Conf.Stdlib do
  @moduledoc """
  THE stdlib gate (plan S5): the real Elixir stdlib compiled from the Elixir
  and OTP beams. It covers IO.puts, Enum over lists and ranges, and String
  basics. The stdout must match BEAM byte for byte.
  """

  def go do
    # IO.puts: literals, computed strings, and interpolation. Interpolation
    # dispatches the String.Chars protocol on integers and binaries.
    IO.puts("hello from mana")
    IO.puts("con" <> "cat" <> "enation")
    n = Enum.sum(1..100)
    IO.puts("sum(1..100) = #{n}")
    IO.puts("atom: #{:some_atom}, int: #{42}")

    # Enum over lists
    IO.puts(Enum.join(Enum.map([1, 2, 3], fn x -> x * 10 end), ","))
    :erlang.display(Enum.map([1, 2, 3], &(&1 + 1)))
    :erlang.display(Enum.filter([1, 2, 3, 4, 5, 6], fn x -> rem(x, 2) == 1 end))
    :erlang.display(Enum.reduce([1, 2, 3, 4], 0, &+/2))
    :erlang.display(Enum.reduce([1, 2, 3], [], fn x, acc -> [x | acc] end))
    :erlang.display(Enum.sort([5, 1, 4, 2, 3]))
    :erlang.display(Enum.sort([5, 1, 4, 2, 3], :desc))
    :erlang.display(Enum.sort_by([{1, :c}, {3, :a}, {2, :b}], fn {_, k} -> k end))
    :erlang.display(Enum.reverse([1, 2, 3]))
    :erlang.display(Enum.member?([1, 2, 3], 2))
    :erlang.display(Enum.count([1, 2, 3]))
    :erlang.display(Enum.at([1, 2, 3], 1))
    :erlang.display(Enum.take([1, 2, 3, 4, 5], 2))
    :erlang.display(Enum.drop([1, 2, 3, 4, 5], 2))
    :erlang.display(Enum.concat([1, 2], [3, 4]))
    :erlang.display(Enum.zip([1, 2, 3], [:a, :b, :c]))
    :erlang.display(Enum.uniq([1, 2, 1, 3, 2]))
    :erlang.display(Enum.max([3, 1, 4]))
    :erlang.display(Enum.min([3, 1, 4]))
    :erlang.display(Enum.all?([1, 2, 3], fn x -> x > 0 end))
    :erlang.display(Enum.any?([1, 2, 3], fn x -> x > 2 end))
    :erlang.display(Enum.with_index([:a, :b]))
    :erlang.display(Enum.flat_map([1, 2], fn x -> [x, x * 2] end))
    :erlang.display(Enum.into([{:a, 1}, {:b, 2}], %{}))

    # Enum over ranges
    :erlang.display(Enum.to_list(1..5))
    :erlang.display(Enum.map(1..4, fn x -> x * x end))
    :erlang.display(Enum.sum(1..10))
    :erlang.display(Enum.filter(1..20, fn x -> rem(x, 5) == 0 end))

    # String basics
    :erlang.display(String.upcase("hello"))
    :erlang.display(String.downcase("HeLLo"))
    :erlang.display(String.length("héllo wörld"))
    :erlang.display(String.split("a,b,,c", ","))
    :erlang.display(String.split("  a b  ", " ", trim: true))
    :erlang.display(String.trim("  padded  "))
    :erlang.display(String.contains?("hello world", "lo w"))
    :erlang.display(String.starts_with?("hello", "he"))
    :erlang.display(String.ends_with?("hello", "lo"))
    :erlang.display(String.replace("a-b-c", "-", "+"))
    :erlang.display(String.slice("hello world", 6, 5))
    :erlang.display(String.reverse("abc"))
    :erlang.display(String.duplicate("ab", 3))
    :erlang.display(String.capitalize("hello"))
    :erlang.display(String.to_integer("1234"))
    :erlang.display(String.first("xyz"))
    :erlang.display(String.at("xyz", 1))
    :erlang.display(String.graphemes("abc"))
    :erlang.display(String.codepoints("héllo"))
    :erlang.display(String.pad_leading("7", 3, "0"))

    # Kernel conversions
    :erlang.display(Integer.to_string(255))
    :erlang.display(Integer.to_string(255, 16))
    :erlang.display(Integer.parse("42abc"))
    :erlang.display(to_string(123))
    :erlang.display(to_string(:an_atom))

    # List module
    :erlang.display(List.first([1, 2, 3]))
    :erlang.display(List.last([1, 2, 3]))
    :erlang.display(List.flatten([1, [2, [3, 4]], 5]))
    :erlang.display(List.to_string([104, 105]))

    # Map module
    m = Map.new([{:a, 1}, {:b, 2}])
    :erlang.display(Map.get(m, :a))
    :erlang.display(Map.get(m, :z, :default))
    :erlang.display(Map.has_key?(m, :b))
    :erlang.display(Map.keys(m))
    :erlang.display(Map.values(m))
    :erlang.display(:maps.size(Map.put(m, :c, 3)))

    # Keyword lists
    kw = [a: 1, b: 2]
    :erlang.display(Keyword.get(kw, :b))
    :erlang.display(Keyword.has_key?(kw, :a))

    # pipes and composition under GC pressure
    total =
      1..200
      |> Enum.map(fn x -> x * 3 end)
      |> Enum.filter(fn x -> rem(x, 2) == 0 end)
      |> Enum.map(&Integer.to_string/1)
      |> Enum.map(&String.length/1)
      |> Enum.sum()

    IO.puts("pipeline total: #{total}")
  end
end
