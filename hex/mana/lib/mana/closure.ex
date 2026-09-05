defmodule Mana.Closure do
  @moduledoc """
  Static dependency closure from the beam import tables (the `ImpT` chunk).
  The closure is the set of modules that the given beams import, directly or
  through other modules. A read of the chunk table costs about one
  millisecond per beam. No debug_info decode is needed.

  Import tables do not show dynamic dispatch (apply/3, protocol impl tables,
  child specs). The compile chase loop finds those modules. Runtime-cut
  modules (`manac --print-bif-modules`) and build-tool beams are never
  followed.
  """

  # eex stays pullable: compiled EEx templates call EEx.Engine at run time.
  @build_tool_re ~r{/(mix|ex_unit|iex)(-[\d.]+)?/ebin/}

  @doc """
  Breadth-first walk of the import closure of `seed_beams` (paths). Returns a
  MapSet of module-name strings that have beams that `:code.which/1` finds
  and that are not build-tool beams. `cut` is a MapSet of module-name strings
  that the walk never follows.
  """
  def modules(seed_beams, cut) do
    walk(seed_beams, cut, MapSet.new(), MapSet.new())
  end

  defp walk([], _cut, _seen, found), do: found

  defp walk([beam | rest], cut, seen, found) do
    new =
      for {m, _f, _a} <- imports(beam),
          ms = Atom.to_string(m),
          not MapSet.member?(cut, ms) and not MapSet.member?(seen, ms),
          uniq: true,
          do: {m, ms}

    seen = Enum.reduce(new, seen, fn {_, ms}, s -> MapSet.put(s, ms) end)

    {beams, found} =
      Enum.reduce(new, {[], found}, fn {m, ms}, {bs, fd} ->
        case :code.which(m) do
          path when is_list(path) ->
            b = List.to_string(path)
            if b =~ @build_tool_re do
              {bs, fd}
            else
              {[b | bs], MapSet.put(fd, ms)}
            end

          # :preloaded, :cover_compiled, or :non_existing
          _ ->
            {bs, fd}
        end
      end)

    walk(beams ++ rest, cut, seen, found)
  end

  defp imports(beam) do
    case :beam_lib.chunks(String.to_charlist(beam), [:imports]) do
      {:ok, {_m, [imports: imps]}} -> imps
      _ -> []
    end
  end
end
