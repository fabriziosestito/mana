defmodule Fib do
  @moduledoc """
  The smallest possible mana program: a single module that uses only `:erlang` BIFs.
  """

  def main do
    :erlang.display(fib(30))
  end

  def fib(0), do: 0
  def fib(1), do: 1
  def fib(n), do: fib(n - 1) + fib(n - 2)
end
