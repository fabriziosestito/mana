defmodule Conf.Fib do
  @moduledoc """
  Conformance program for recursion, arithmetic, tuples, lists, and
  comparisons.

  Every conformance program is a `Conf.*` module with a `go/0` that prints
  with `:erlang.display/1`. The harness runs it on BEAM and as a mana native
  binary and asserts that the outputs are identical.
  """

  def go do
    :erlang.display(fib(20))
    :erlang.display(fib(1))
    :erlang.display({:fib, 10, fib(10)})
    :erlang.display([fib(5), fib(6), fib(7)])
    :erlang.display(fib(10) > fib(9))
    :erlang.display(rem(fib(15), 7))
  end

  defp fib(0), do: 0
  defp fib(1), do: 1
  defp fib(n), do: fib(n - 1) + fib(n - 2)
end
