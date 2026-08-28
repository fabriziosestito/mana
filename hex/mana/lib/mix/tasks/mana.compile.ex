defmodule Mix.Tasks.Mana.Compile do
  @shortdoc "Compile this project to a native binary via manac"

  @moduledoc """
  Compile this Mix project to a native binary with the mana compiler.

      mix mana.compile --entry Mod.fun/0 [--out DIR] [--bin PATH]

  The entry must be a zero-arity function; the produced binary runs it and
  exits. Accepted entry formats: `Mod.fun/0`, `Nested.Mod.fun/0`,
  `mod:fun/0` (Erlang-style, module taken verbatim).

  Current limitations (early days): the entry module must be
  self-contained — it may call only `:erlang` BIFs supported by the mana
  runtime, not other modules or the Elixir standard library.

  Output goes to `_mana/` by default: the extracted `.core` file (kept for
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

    beam = beam_path!(mod)
    core = Path.join(out, "#{mod}.core")
    Mana.CoreDump.dump!(beam, core)

    manac = Mana.compiler_path(bin: opts[:bin])
    app = Path.join(out, "app")
    args = ["--entry", "#{fun}/#{arity}", "-o", app, core]

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

  defp beam_path!(mod) do
    path = Path.join(Mix.Project.compile_path(), "#{mod}.beam")

    if File.exists?(path) do
      path
    else
      Mix.raise("no compiled module #{inspect(mod)} at #{path}")
    end
  end
end
