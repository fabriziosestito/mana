defmodule Conf.Inspect.Point do
  defstruct x: 0, y: 0, label: nil
end

defmodule Conf.Inspect do
  @moduledoc """
  The Inspect protocol end to end: inspect/1 and IO.inspect through
  Inspect.Algebra, Code.Identifier, and the leaf impls. The program uses
  small maps only, because the flatmap key order matches the sorted order
  of BEAM. It uses no pids, refs, or funs, because their rendering is
  nondeterministic.
  """

  def go do
    # integers and floats
    IO.puts(inspect(0))
    IO.puts(inspect(-42))
    IO.puts(inspect(1_152_921_504_606_846_975))
    IO.puts(inspect(3.14))
    IO.puts(inspect(-0.5))
    IO.puts(inspect(1.0e20))
    IO.puts(inspect(1.0))

    # atoms
    IO.puts(inspect(:ok))
    IO.puts(inspect(:"quoted atom"))
    IO.puts(inspect(:"Elixir.String.Chars"))
    IO.puts(inspect(SomeAlias.Nested))
    IO.puts(inspect(true))
    IO.puts(inspect(false))
    IO.puts(inspect(nil))
    IO.puts(inspect(:%{}))
    IO.puts(inspect(:+))

    # binaries and strings
    IO.puts(inspect("hello"))
    IO.puts(inspect("with \"quotes\" and \n newline"))
    IO.puts(inspect("unicode: héllo ünïcode"))
    IO.puts(inspect(<<0, 255, 128>>))
    IO.puts(inspect(<<"abc", 0>>))
    IO.puts(inspect(""))

    # charlists
    IO.puts(inspect(~c"abc"))
    IO.puts(inspect([104, 105]))
    IO.puts(inspect([0, 1, 2]))

    # lists
    IO.puts(inspect([]))
    IO.puts(inspect([1, 2, 3]))
    IO.puts(inspect([1, [2, [3, []]], :x]))
    IO.puts(inspect([1 | 2]))
    IO.puts(inspect([a: 1, b: "two", c: :three]))
    IO.puts(inspect([{:a, 1}, {"not", "kw"}]))

    # tuples
    IO.puts(inspect({}))
    IO.puts(inspect({:ok, 1}))
    IO.puts(inspect({:error, {:nested, [1, 2]}, "msg"}))

    # Maps: small, so the sorted flatmap order is deterministic on both sides.
    IO.puts(inspect(%{}))
    IO.puts(inspect(%{a: 1}))
    IO.puts(inspect(%{a: 1, b: 2, z: 26}))
    IO.puts(inspect(%{"bin" => 1, "key" => 2}))
    IO.puts(inspect(%{1 => :one, 2 => :two}))
    IO.puts(inspect(%{{:t, 1} => [:v], :atom => %{nested: true}}))

    # structs
    IO.puts(inspect(%Conf.Inspect.Point{}))
    IO.puts(inspect(%Conf.Inspect.Point{x: 1, y: -2, label: "origin"}))

    # ranges
    IO.puts(inspect(1..10))
    IO.puts(inspect(10..1//-2))

    # options
    IO.puts(inspect([1, 2, 3, 4, 5], limit: 3))
    IO.puts(inspect(%{a: [1, 2, 3]}, pretty: true, width: 10))
    IO.puts(inspect("no quotes", binaries: :as_binaries))
    IO.puts(inspect([104, 105], charlists: :as_lists))

    # IO.inspect returns its argument and supports label:.
    x = IO.inspect({:passthrough, 1}, label: "lbl")
    IO.puts(inspect(x == {:passthrough, 1}))

    # inspect inside interpolation
    IO.puts("value: #{inspect(%{k: :v})}")

    :ok
  end
end
