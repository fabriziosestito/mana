defmodule Conf.Funs do
  @moduledoc """
  Conformance program: closures — anonymous funs, captures, funs as
  arguments, fun references (`&f/1`), and closures returning closures.
  """

  def go do
    double = fn x -> x * 2 end
    :erlang.display(double.(21))

    k = 10
    add_k = fn x -> x + k end
    :erlang.display(add_k.(5))

    :erlang.display(my_map([1, 2, 3], double))
    :erlang.display(my_map([1, 2, 3], &triple/1))

    make_adder = fn n -> fn x -> x + n end end
    add3 = make_adder.(3)
    :erlang.display(add3.(4))
    :erlang.display(my_map([10, 20], make_adder.(1)))

    pick = fn
      {:a, x} -> x
      {:b, x} -> x * 2
    end

    :erlang.display(pick.({:a, 7}))
    :erlang.display(pick.({:b, 7}))
  end

  defp triple(x), do: x * 3

  defp my_map([], _f), do: []
  defp my_map([h | t], f), do: [f.(h) | my_map(t, f)]
end
