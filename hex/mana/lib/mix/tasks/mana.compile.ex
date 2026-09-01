defmodule Mix.Tasks.Mana.Compile do
  @shortdoc "Compile this project to a native binary via manac"

  @moduledoc """
  Compile this Mix project to a native binary with the mana compiler.

      mix mana.compile --entry Mod.fun/0 [--out DIR] [--bin PATH]
      mix mana.compile --app [--out DIR] [--bin PATH]

  The entry must be a zero-arity function; the produced binary runs it and
  exits. Accepted entry formats: `Mod.fun/0`, `Nested.Mod.fun/0`,
  `mod:fun/0` (Erlang-style, module taken verbatim).

  `--app` instead boots the project like a release: a generated
  `Mana.AppBoot` module bakes the compile-time config and starts the
  application dependency tree in order, then parks (see `Mana.Boot`).

  Current limitations (early days): modules of this project may call each
  other and supported `:erlang` BIFs, but the Elixir/Erlang standard library
  and Hex dependencies are not available yet.

  Output goes to `_mana/` by default: the extracted `.core` files (kept for
  debugging) and the final binary `_mana/app`.
  """

  use Mix.Task

  @switches [entry: :string, out: :string, bin: :string, app: :boolean]

  @impl true
  def run(argv) do
    {opts, _argv, _errors} = OptionParser.parse(argv, switches: @switches)

    # native builds get release init semantics: plug_init_mode :runtime is a
    # dev/code-reloading affordance that resolves plug modules through
    # runtime-built atoms — invisible to closed-world reachability. Forcing
    # :compile bakes plug opts (module atoms as literals) into the beams;
    # Mix's compile-env tracking recompiles affected modules automatically.
    Application.put_env(:phoenix, :plug_init_mode, :compile)

    # Apply project config once, WITHOUT compile-env validation (beams
    # compiled with the scrub below legitimately disagree with the config
    # files' dev-only keys), then scrub dev-only build-tool config
    # (code_reloader etc.) so compile_env consumers bake release
    # semantics. Mix.Task.run dedups: the compile below won't re-apply
    # config over the scrub.
    Mix.Task.run("loadpaths", ["--no-validate-compile-env"])
    Mana.Boot.scrub_compile_env!()

    # Mix's staleness checks verify compile_env against the CONFIG FILES,
    # not runtime put_env — so beams compiled before these overrides keep
    # the old semantics. A versioned marker under the build dir forces one
    # full recompile per build dir whenever the override set changes.
    marker = Path.join(Mix.Project.build_path(), "mana_init_mode")
    stamp = "plug_init_mode=compile scrub=v1"

    if File.read(marker) == {:ok, stamp} do
      Mix.Task.run("compile")
    else
      Mix.Task.run("compile", ["--force"])
      File.write!(marker, stamp)
    end

    if opts[:app] && opts[:entry] do
      Mix.raise("--app and --entry are mutually exclusive")
    end

    out = Path.expand(opts[:out] || "_mana")
    File.mkdir_p!(out)

    # Dump every module of the project; manac compiles only what the entry
    # reaches (and only errors on parse failures of modules it needs).
    beams = Path.wildcard(Path.join(Mix.Project.compile_path(), "*.beam"))

    if beams == [] do
      Mix.raise("no compiled modules under #{Mix.Project.compile_path()}")
    end

    # --app: release-style boot — generate Mana.AppBoot (baked config +
    # ordered application starts) and make it the entry
    {mod, fun, arity, beams} =
      if opts[:app] do
        boot_beam = Mana.Boot.generate!(out)
        {Mana.AppBoot, :main, 0, beams ++ [boot_beam]}
      else
        {mod, fun, arity} = resolve_entry!(opts[:entry])
        entry_beam = Path.join(Mix.Project.compile_path(), "#{mod}.beam")

        unless entry_beam in beams do
          Mix.raise("no compiled module #{inspect(mod)} at #{entry_beam}")
        end

        {mod, fun, arity, beams}
      end

    cores =
      for beam <- beams do
        core = Path.join(out, Path.basename(beam, ".beam") <> ".core")
        dump_if_stale(beam, core)
        core
      end

    # application-own modules keep every export (release semantics):
    # the project's modules plus any PATH dependency (local apps wired by
    # config atoms / template-name dispatch). Hex deps stay pruned.
    path_dep_mods =
      for {dep_app, dep_path} <- Mix.Project.deps_paths(),
          not String.starts_with?(Path.expand(dep_path), Path.expand(Mix.Project.deps_path())),
          beam <-
            Path.wildcard(
              Path.join(Mix.Project.build_path(), "lib/#{dep_app}/ebin/*.beam")
            ),
          uniq: true,
          do: Path.basename(beam, ".beam")

    own_mods = Enum.map(beams, &Path.basename(&1, ".beam"))

    seed_args =
      (own_mods ++ path_dep_mods)
      |> Enum.uniq()
      |> Enum.reject(&String.contains?(&1, "Elixir.Mix."))
      |> Enum.flat_map(&["--seed-exports", &1])

    manac = Mana.compiler_path(bin: opts[:bin])
    app = Path.join(out, "app")

    # runtime-implemented modules the closure BFS must never follow —
    # single source of truth lives in manac
    {cut_out, 0} = System.cmd(manac, ["--print-bif-modules"])
    cut = MapSet.new(String.split(cut_out, "\n", trim: true))

    # warm start: the manifest memoizes the last successful build's full
    # core list, so a rebuild starts complete and compiles in one round.
    # The chase fallback still finds anything new via locate_and_dump.
    have = MapSet.new(cores, &core_module/1)

    {cores, have} =
      Enum.reduce(read_manifest(out), {cores, have}, fn core, {cs, hv} ->
        m = core_module(core)

        if MapSet.member?(hv, m) or not File.exists?(core) do
          {cs, hv}
        else
          {cs ++ [core], MapSet.put(hv, m)}
        end
      end)

    compile_loop(manac, mod, fun, arity, app, cores, out, MapSet.new(), 400, seed_args, cut, have)
  end

  # Reachability-driven stdlib compilation: run manac; when it reports a
  # missing module that we can locate on the code path (Elixir stdlib, OTP
  # stdlib/kernel, deps — anything loadable), dump its Core Erlang — AND its
  # whole static import closure, so one round absorbs the whole subgraph —
  # into the cache and retry. Only modules the entry reaches get pulled in.
  defp compile_loop(manac, mod, fun, arity, app, cores, out, tried, fuel, seed_args, cut, have) do
    args = ["--entry", "#{mod}:#{fun}/#{arity}", "-o", app] ++ seed_args ++ cores
    t0 = System.monotonic_time(:millisecond)
    {output, status} = System.cmd(manac, args, stderr_to_stdout: true)

    if System.get_env("MANA_DEBUG_LOOP") do
      ms = System.monotonic_time(:millisecond) - t0
      chars = Enum.count(cores, &String.contains?(&1, "Chars.Integer"))
      time = Enum.find(String.split(output, "\n"), &String.starts_with?(&1, "manac: time:"))

      IO.puts(
        "mana-loop: status=#{status} cores=#{length(cores)} chars_int=#{chars} fuel=#{fuel} ms=#{ms}#{if time, do: " | " <> time, else: ""}"
      )
    end

    cond do
      status == 0 ->
        # even a successful build may name dynamic-dispatch candidates
        # (consolidated protocol impls) it could not see; pull the ones a
        # beam exists for and rebuild
        candidates =
          (Regex.scan(~r/dynamic module candidate '([^']+)'/, output) ++
             Regex.scan(~r/module '([^']+)' \(required by .*\) is not among/, output))
          |> Enum.map(fn [_, m] -> m end)
          |> Enum.uniq()
          |> Enum.reject(&(MapSet.member?(tried, &1) or MapSet.member?(have, &1)))

        {pulled, tried, have} = pull_all(candidates, out, cut, tried, have, " (dynamic)")

        if pulled == [] or fuel == 0 do
          IO.write(output)
          write_manifest(out, cores)
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
            tried,
            fuel - 1,
            seed_args,
            cut,
            have
          )
        end

      fuel == 0 ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status}); dependency chase gave up")

      (missing =
         missing_modules(output)
         |> Enum.reject(&(MapSet.member?(tried, &1) or MapSet.member?(have, &1)))) != [] ->
        {pulled, tried, have} = pull_all(missing, out, cut, tried, have, "")

        if pulled == [] do
          IO.write(output)
          Mix.raise("manac failed (exit #{status}) — see output above")
        end

        compile_loop(
          manac,
          mod,
          fun,
          arity,
          app,
          pulled ++ cores,
          out,
          tried,
          fuel - 1,
          seed_args,
          cut,
          have
        )

      true ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status})")
    end
  end

  # Pull each module's core plus its whole static import closure (beam
  # ImpT chunks) — one chase round absorbs the entire subgraph instead of
  # one dependency layer per round.
  defp pull_all(mods, out, cut, tried, have, tag) do
    expanded =
      mods
      |> Enum.flat_map(fn m ->
        case locate_beam(m) do
          {:ok, beam} -> [m | MapSet.to_list(Mana.Closure.modules([beam], cut))]
          :error -> [m]
        end
      end)
      |> Enum.uniq()
      |> Enum.reject(&(MapSet.member?(have, &1) or (&1 not in mods and MapSet.member?(tried, &1))))

    pulled =
      for m <- expanded, {:ok, core} <- [locate_and_dump(m, out)] do
        Mix.shell().info("mana: pulling in #{m}#{tag}")
        {m, core}
      end

    tried = Enum.reduce(mods ++ expanded, tried, &MapSet.put(&2, &1))
    have = Enum.reduce(pulled, have, fn {m, _}, h -> MapSet.put(h, m) end)
    {Enum.map(pulled, &elem(&1, 1)), tried, have}
  end

  defp missing_modules(output) do
    Regex.scan(~r/module '([^']+)' \(required by .*\) is not among the compiled/, output)
    |> Enum.map(fn [_, m] -> m end)
    |> Enum.uniq()
  end

  defp locate_and_dump(module, out) do
    case locate_beam(module) do
      {:ok, beam} ->
        # toolchain beams (outside this project's build) → shared cache;
        # project-local ones (consolidated protocols etc.) → out dir
        cache =
          if String.starts_with?(beam, Mix.Project.build_path()) do
            Path.join(out, "core-cache")
          else
            shared_cache_dir()
          end

        File.mkdir_p!(cache)
        core = Path.join(cache, module <> ".core")
        dump_if_stale(beam, core)
        {:ok, core}

      :error ->
        :error
    end
  end

  defp locate_beam(module) do
    case :code.which(String.to_atom(module)) do
      beam_path when is_list(beam_path) ->
        beam = List.to_string(beam_path)

        # build-tool applications never belong in a runtime binary; their
        # protocol impls (Collectable.Mix.Shell, ...) stay unimplemented.
        # eex is NOT one of them: compiled EEx templates call EEx.Engine
        # at runtime (Plug.Debugger error pages).
        if beam =~ ~r{/(mix|ex_unit|iex)(-[\d.]+)?/ebin/} do
          :error
        else
          {:ok, beam}
        end

      _ ->
        :error
    end
  end

  # core dumps are pure functions of the beam: skip when the core is newer
  defp dump_if_stale(beam, core) do
    fresh? =
      case {File.stat(core, time: :posix), File.stat(beam, time: :posix)} do
        {{:ok, %{mtime: c}}, {:ok, %{mtime: b}}} -> c >= b
        _ -> false
      end

    unless fresh?, do: Mana.CoreDump.dump!(beam, core)
  end

  defp core_module(core), do: Path.basename(core, ".core")

  # out/manifest: the last successful build's full core list, so a warm
  # rebuild starts complete and compiles in one round. Keyed to the
  # toolchain — core dumps are toolchain-version functions of the beams.
  defp manifest_header, do: "mana-manifest v1 #{System.version()}-otp#{System.otp_release()}"

  defp read_manifest(out) do
    case File.read(Path.join(out, "manifest")) do
      {:ok, content} ->
        header = manifest_header()

        case String.split(content, "\n", trim: true) do
          [^header | cores] -> cores
          _ -> []
        end

      _ ->
        []
    end
  end

  defp write_manifest(out, cores) do
    File.write!(
      Path.join(out, "manifest"),
      Enum.join([manifest_header() | Enum.uniq(cores)], "\n") <> "\n"
    )
  end

  # <user cache>/mana/cores/<elixir>-otp<otp>: core dumps are pure
  # functions of the beam, so one cache per toolchain serves every project.
  # :filename.basedir follows each OS's convention (XDG on Linux,
  # ~/Library/Caches on macOS, Local AppData on Windows); MANA_CACHE_DIR
  # overrides, and manac's object cache honors the same variable.
  defp shared_cache_dir do
    base =
      case System.get_env("MANA_CACHE_DIR") do
        nil -> List.to_string(:filename.basedir(:user_cache, ~c"mana"))
        dir -> dir
      end

    Path.join([base, "cores", "#{System.version()}-otp#{System.otp_release()}"])
  end

  defp resolve_entry!(nil) do
    Mix.raise("--entry Mod.fun/0 or --app is required")
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
