defmodule Conf.MultiHelper do
  @moduledoc false

  def tag, do: :hello
  def add(a, b), do: a + b
  def pair(x), do: {:pair, x}
end

defmodule Conf.Multi do
  @moduledoc """
  Conformance program for cross-module calls and, above all, cross-module
  atom identity. `tag() == :hello` compares an atom created in the object
  of MultiHelper against one created in the object of this module.
  """

  def go do
    :erlang.display(Conf.MultiHelper.add(40, 2))
    :erlang.display(Conf.MultiHelper.tag())
    :erlang.display(Conf.MultiHelper.tag() == :hello)
    :erlang.display(Conf.MultiHelper.pair([1, 2, 3]))
    :erlang.display(Conf.MultiHelper.add(Conf.MultiHelper.add(1, 2), 3))
  end
end
