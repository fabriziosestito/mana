defmodule Bench.EctoLoop do
  @moduledoc """
  Profiling vehicle for the changeset pipeline: a plain tight loop around
  `Bench.Ecto.User.changeset/2` with no benchee machinery, so callgrind
  profiles attribute cost to the pipeline itself. `Bench.Ecto` (benchee)
  stays the official scoreboard.
  """
  alias Bench.Ecto.User

  @iters 50_000
  @attrs %{"name" => "Ada", "email" => "ada@example.com", "age" => 36}
  @bad %{"name" => "A", "age" => 200}

  def run do
    {us_valid, n_valid} = :timer.tc(fn -> loop(@iters, @attrs, 0) end)
    {us_invalid, n_invalid} = :timer.tc(fn -> loop(@iters, @bad, 0) end)
    :io.format("valid:   ~.3f us/iter (~p valid)~n", [us_valid / @iters, n_valid])
    :io.format("invalid: ~.3f us/iter (~p valid)~n", [us_invalid / @iters, n_invalid])
    :ok
  end

  defp loop(0, _attrs, acc), do: acc

  defp loop(n, attrs, acc) do
    cs = User.changeset(%User{}, attrs)
    acc = if cs.valid?, do: acc + 1, else: acc
    loop(n - 1, attrs, acc)
  end
end
