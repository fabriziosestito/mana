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
    # warm start: previously chased stdlib cores (unreached ones are free —
    # manac only compiles what the entry needs)
    cached = Path.wildcard(Path.join([out, "core-cache", "*.core"]))
    compile_loop(manac, mod, fun, arity, app, cached ++ cores, out, MapSet.new(), 400)
  end

  # Reachability-driven stdlib compilation: run manac; when it reports a
  # missing module that we can locate on the code path (Elixir stdlib, OTP
  # stdlib/kernel, deps — anything loadable), dump its Core Erlang into the
  # cache and retry. Only modules the entry actually reaches get pulled in.
  defp compile_loop(manac, mod, fun, arity, app, cores, out, tried, fuel) do
    args = ["--entry", "#{mod}:#{fun}/#{arity}", "-o", app] ++ cores
    {output, status} = System.cmd(manac, args, stderr_to_stdout: true)

    if System.get_env("MANA_DEBUG_LOOP") do
      chars = Enum.count(cores, &String.contains?(&1, "Chars.Integer"))
      IO.puts("mana-loop: status=#{status} cores=#{length(cores)} chars_int=#{chars} fuel=#{fuel}")
    end

    cond do
      status == 0 ->
        # even a successful build may name dynamic-dispatch candidates
        # (consolidated protocol impls) it could not see; pull the ones a
        # beam exists for and rebuild
        candidates =
          Regex.scan(~r/dynamic module candidate '([^']+)'/, output)
          |> Enum.map(fn [_, m] -> m end)
          |> Enum.uniq()
          |> Enum.reject(&MapSet.member?(tried, &1))

        pulled =
          for m <- candidates,
              {:ok, core} <- [locate_and_dump(m, out)] do
            Mix.shell().info("mana: pulling in #{m} (dynamic)")
            core
          end

        if pulled == [] or fuel == 0 do
          IO.write(output)
          :ok
        else
          compile_loop(
            manac,
            mod,
            fun,
            arity,
            app,
            pulled ++ cores,
            out,
            Enum.reduce(candidates, tried, &MapSet.put(&2, &1)),
            fuel - 1
          )
        end

      fuel == 0 ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status}); dependency chase gave up")

      (missing = missing_modules(output)) != [] ->
        if Enum.any?(missing, &MapSet.member?(tried, &1)) do
          IO.write(output)
          Mix.raise("manac failed (exit #{status}): module loop in #{inspect(missing)}")
        end

        pulled =
          for m <- missing do
            case locate_and_dump(m, out) do
              {:ok, core} ->
                Mix.shell().info("mana: pulling in #{m}")
                core

              :error ->
                IO.write(output)
                Mix.raise("manac failed (exit #{status}): cannot locate module '#{m}'")
            end
          end

        compile_loop(
          manac,
          mod,
          fun,
          arity,
          app,
          pulled ++ cores,
          out,
          Enum.reduce(missing, tried, &MapSet.put(&2, &1)),
          fuel - 1
        )

      true ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status})")
    end
  end

  defp missing_modules(output) do
    Regex.scan(~r/module '([^']+)' \(required by [^)]+\) is not among the compiled/, output)
    |> Enum.map(fn [_, m] -> m end)
    |> Enum.uniq()
  end

  defp locate_and_dump(module, out) do
    do_locate_and_dump(module, out)
  catch
    :build_tool -> :error
  end

  defp do_locate_and_dump(module, out) do
    cache = Path.join(out, "core-cache")
    File.mkdir_p!(cache)
    core = Path.join(cache, module <> ".core")

    case :code.which(String.to_atom(module)) do
      beam_path when is_list(beam_path) ->
        beam = List.to_string(beam_path)

        # build-tool applications never belong in a runtime binary; their
        # protocol impls (Collectable.Mix.Shell, ...) stay unimplemented
        if beam =~ ~r{/(mix|ex_unit|iex|eex)(-[\d.]+)?/ebin/} do
          throw(:build_tool)
        end

        fresh? =
          case {File.stat(core, time: :posix), File.stat(beam, time: :posix)} do
            {{:ok, %{mtime: c}}, {:ok, %{mtime: b}}} -> c >= b
            _ -> false
          end

        unless fresh?, do: Mana.CoreDump.dump!(beam, core)
        {:ok, core}

      _ ->
        :error
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
