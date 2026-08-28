defmodule Mix.Tasks.Mana.Compile do
  @shortdoc "Compile this project to a native binary via manac"

  @moduledoc """
  Compile this Mix project to a native binary with the mana compiler.

      mix mana.compile --entry Mod.fun/0 [--out DIR] [--bin PATH]

  The entry must be a zero-arity function; the produced binary runs it and
  exits. Accepted entry formats: `Mod.fun/0`, `Nested.Mod.fun/0`,
  `mod:fun/0` (Erlang-style, module taken verbatim).

  Current limitations (early days): modules of this project may call each
  other and supported `:erlang` BIFs, but the Elixir/Erlang standard library
  and Hex dependencies are not available yet.

  Output goes to `_mana/` by default: the extracted `.core` files (kept for
  debugging) and the final binary `_mana/app`.
  """

  use Mix.Task

  @switches [entry: :string, out: :string, bin: :string]

  @impl true
  def run(argv) do
    {opts, _argv, _errors} = OptionParser.parse(argv, switches: @switches)

    Mix.Task.run("compile")

    {mod, fun, arity} = resolve_entry!(opts[:entry])
    out = Path.expand(opts[:out] || "_mana")
    File.mkdir_p!(out)

    # Dump every module of the project; manac compiles only what the entry
    # reaches (and only errors on parse failures of modules it needs).
    beams = Path.wildcard(Path.join(Mix.Project.compile_path(), "*.beam"))

    if beams == [] do
      Mix.raise("no compiled modules under #{Mix.Project.compile_path()}")
    end

    entry_beam = Path.join(Mix.Project.compile_path(), "#{mod}.beam")

    unless entry_beam in beams do
      Mix.raise("no compiled module #{inspect(mod)} at #{entry_beam}")
    end

    cores =
      for beam <- beams do
        core = Path.join(out, Path.basename(beam, ".beam") <> ".core")
        Mana.CoreDump.dump!(beam, core)
        core
      end

    manac = Mana.compiler_path(bin: opts[:bin])
    app = Path.join(out, "app")
    args = ["--entry", "#{mod}:#{fun}/#{arity}", "-o", app] ++ cores

    case System.cmd(manac, args, stderr_to_stdout: true, into: IO.stream(:stdio, :line)) do
      {_, 0} -> :ok
      {_, status} -> Mix.raise("manac failed (exit #{status})")
    end
  end

  defp resolve_entry!(nil) do
    Mix.raise("--entry Mod.fun/0 is required (OTP application entry points come later)")
  end

  defp resolve_entry!(entry) do
    with [mf, arity_str] <- String.split(entry, "/"),
         {arity, ""} <- Integer.parse(arity_str),
         {:ok, mod, fun} <- split_mod_fun(mf) do
      if arity != 0 do
        Mix.raise("entry function must have arity 0, got #{entry}")
      end

      {mod, fun, arity}
    else
      _ -> Mix.raise("bad --entry #{inspect(entry)}: expected Mod.fun/0")
    end
  end

  defp split_mod_fun(mf) do
    cond do
      String.contains?(mf, ":") ->
        [m, f] = String.split(mf, ":", parts: 2)
        {:ok, String.to_atom(m), String.to_atom(f)}

      String.contains?(mf, ".") ->
        parts = String.split(mf, ".")
        {fun, mods} = List.pop_at(parts, -1)
        {:ok, Module.concat(mods), String.to_atom(fun)}

      true ->
        :error
    end
  end
end
