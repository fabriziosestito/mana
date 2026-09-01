defmodule Mana.Closure do
  @moduledoc """
  Static dependency closure from beam import tables (the `ImpT` chunk):
  the set of modules transitively imported by the given beams. Reading the
  chunk table costs about a millisecond per beam — no debug_info decode.

  Dynamic dispatch (apply/3, protocol impl tables, child specs) is
  invisible to import tables; the compile chase loop discovers those as
  before. Runtime-cut modules (`manac --print-bif-modules`) and build-tool
  beams are never followed.
  """

  # eex stays pullable: compiled EEx templates call EEx.Engine at runtime
  @build_tool_re ~r{/(mix|ex_unit|iex)(-[\d.]+)?/ebin/}

  @doc """
  BFS the import closure of `seed_beams` (paths). Returns a MapSet of
  module-name strings that have locatable, non-build-tool beams. `cut` is
  a MapSet of module-name strings to never follow.
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

          # :preloaded / :cover_compiled / :non_existing
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
