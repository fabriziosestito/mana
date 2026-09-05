defmodule Mix.Tasks.Mana.Compile do
  @shortdoc "Compile this project to a native binary with manac"

  @moduledoc """
  Compile this Mix project to a native binary with the mana compiler.

      mix mana.compile --entry Mod.fun/0 [--out DIR] [--bin PATH]
      mix mana.compile --app [--out DIR] [--bin PATH]

  The entry must be a zero-arity function. The binary runs this function and
  exits. The task accepts these entry formats: `Mod.fun/0`, `Nested.Mod.fun/0`,
  and `mod:fun/0` (Erlang style, the module name is used as written).

  `--app` boots the project like a release. A generated `Mana.AppBoot` module
  bakes the compile-time config and starts the application dependency tree in
  order. Then it parks (see `Mana.Boot`).

  The standard library and the Hex dependencies arrive through the chase
  loop: the task pulls every module that `manac` reports as missing, dumps
  its Core Erlang, and compiles again. A manifest records the final module
  list, so the next build runs in one pass.

  Output goes to `_mana/` by default. It holds the extracted `.core` files
  (kept for debugging) and the final binary `_mana/app`.
  """

  use Mix.Task

  @switches [entry: :string, out: :string, bin: :string, app: :boolean]

  @impl true
  def run(argv) do
    {opts, _argv, _errors} = OptionParser.parse(argv, switches: @switches)

    # Native builds get release init semantics. plug_init_mode :runtime is a
    # dev and code-reloading feature. It resolves plug modules through atoms
    # built at run time. Closed-world reachability cannot see those atoms.
    # The forced :compile mode bakes plug opts (module atoms as literals) into
    # the beams. The compile-env tracking of Mix recompiles the affected
    # modules.
    Application.put_env(:phoenix, :plug_init_mode, :compile)

    # Apply the project config once, WITHOUT compile-env validation. Beams
    # compiled with the scrub below differ from the dev-only keys of the
    # config files, and this is correct. Then scrub the dev-only build-tool
    # config (code_reloader and similar keys), so that compile_env consumers
    # bake release semantics. Mix.Task.run dedups: the compile below will not
    # apply the config again over the scrub.
    Mix.Task.run("loadpaths", ["--no-validate-compile-env"])
    Mana.Boot.scrub_compile_env!()

    # The staleness checks of Mix compare compile_env against the CONFIG
    # FILES, not against put_env at run time. So beams compiled before these
    # overrides keep the old semantics. A versioned marker under the build dir
    # forces one full recompile per build dir when the override set changes.
    #
    # The scrub above runs before every compile. So any module that Mix DOES
    # recompile here bakes release semantics. The hazard is a module compiled
    # earlier WITHOUT the scrub, which Mix now considers up to date. A plain
    # `mix compile` or `mix phx.server` in dev does this. This is the
    # browser-demo workflow. To detect this case, compare the mtime of the
    # marker against the newest project beam. A beam newer than the marker was
    # compiled outside this task (unscrubbed). Then force a full recompile.
    marker = Path.join(Mix.Project.build_path(), "mana_init_mode")
    stamp = "plug_init_mode=compile scrub=v1"

    if File.read(marker) == {:ok, stamp} and marker_fresh?(marker) do
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

    # Dump every module of the project. manac compiles only what the entry
    # reaches, and reports parse errors only for the modules that it needs.
    beams = Path.wildcard(Path.join(Mix.Project.compile_path(), "*.beam"))

    if beams == [] do
      Mix.raise("no compiled modules under #{Mix.Project.compile_path()}")
    end

    # --app is a release-style boot. Generate Mana.AppBoot (baked config plus
    # ordered application starts) and make it the entry.
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

    # Modules that belong to the application keep every export (release
    # semantics). These are the modules of the project plus any PATH
    # dependency (local apps wired by config atoms or template-name
    # dispatch). Hex deps stay pruned.
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

    # Find the deps that ship native/ crates (mana_native: metadata) and build
    # them with cargo. Then produce the manac native manifest plus the
    # --native-obj link inputs. Native modules are cut. The closure walk must
    # skip them.
    {native_args, native_mods} = build_native_deps!(out)

    # Modules that the runtime implements. The closure walk must never follow
    # them. manac is the single source of truth for this list.
    {cut_out, 0} = System.cmd(manac, ["--print-bif-modules"])
    cut = MapSet.union(MapSet.new(String.split(cut_out, "\n", trim: true)), native_mods)

    # Warm start: the manifest memoizes the full core list of the last
    # successful build. So a rebuild starts complete and compiles in one
    # round. The chase fallback still finds anything new through
    # locate_and_dump.
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

    compile_loop(manac, mod, fun, arity, app, cores, out, MapSet.new(), 400, seed_args, cut, have, native_args)
  end

  # Walk the deps for `mana_native:` metadata. Build each native crate with
  # cargo. Write the manac native manifest and collect the --native-obj static
  # libs. Returns {manac_native_args, native_module_set}.
  defp build_native_deps!(out) do
    entries =
      for {dep_app, dep_path} <- Mix.Project.deps_paths(),
          pkg <- native_packages(dep_app, dep_path) do
        pkg
      end

    if entries == [] do
      {[], MapSet.new()}
    else
      {libs, lines, mods} =
        Enum.reduce(entries, {[], [], []}, fn %{module: mod, src: src, dep_path: dp},
                                              {libs, lines, mods} ->
          lib = build_native_crate!(Path.join(dp, src), mod)

          fn_lines =
            for {fun, ar} <- native_exports(mod) do
              # Conservative default effects: may_gc and may_raise are always
              # safe. A valid term never equals the exception sentinel.
              "#{mod} #{fun} #{ar} #{mod}_#{fun}_#{ar} 1 1"
            end

          {[lib | libs], fn_lines ++ lines, [mod | mods]}
        end)

      manifest = Path.join(out, "_manac_native.manifest")
      File.write!(manifest, Enum.join(lines, "\n") <> "\n")

      args = ["--native-manifest", manifest] ++ Enum.flat_map(libs, &["--native-obj", &1])
      {args, MapSet.new(mods)}
    end
  end

  defp native_packages(dep_app, dep_path) do
    mix_exs = Path.join(dep_path, "mix.exs")

    if File.exists?(mix_exs) do
      try do
        Mix.Project.in_project(dep_app, dep_path, fn _ ->
          case Keyword.get(Mix.Project.config(), :mana_native) do
            nil ->
              []

            opts ->
              for {name, attrs} <- Keyword.get(opts, :packages, []) do
                %{
                  module: Keyword.fetch!(attrs, :module),
                  src: Keyword.get(attrs, :src, Path.join("native", Atom.to_string(name))),
                  dep_path: dep_path
                }
              end
          end
        end)
      rescue
        _ -> []
      end
    else
      []
    end
  end

  defp build_native_crate!(crate_dir, mod) do
    unless File.dir?(crate_dir) do
      Mix.raise("native crate dir missing: #{crate_dir}")
    end

    Mix.shell().info("==> cargo build --release (native #{mod}) in #{crate_dir}")

    {out, status} =
      System.cmd("cargo", ["build", "--release"],
        cd: crate_dir,
        stderr_to_stdout: true
      )

    if status != 0, do: Mix.raise("cargo build failed for #{crate_dir}:\n#{out}")

    lib = Path.join([crate_dir, "target", "release", "lib#{mod}.a"])
    unless File.exists?(lib), do: Mix.raise("native static lib not found: #{lib}")
    lib
  end

  # The native functions to bind are the exports of the stub module minus the
  # ones that BEAM and Elixir generate. Symbol convention: <module>_<fun>_<arity>.
  defp native_exports(mod) do
    m = String.to_atom(mod)
    Code.ensure_loaded(m)

    m.module_info(:exports)
    |> Enum.reject(fn {fun, _ar} ->
      s = Atom.to_string(fun)
      fun in [:module_info, :__info__, :__mana_native__] or String.starts_with?(s, "__")
    end)
  end

  # Reachability-driven stdlib compilation. Run manac. When it reports a
  # missing module that exists on the code path (Elixir stdlib, OTP stdlib
  # and kernel, deps, anything loadable), dump its Core Erlang into the cache
  # and retry. The dump includes the whole static import closure of the
  # module, so that one round absorbs the whole subgraph. Only modules that
  # the entry reaches are pulled in.
  defp compile_loop(manac, mod, fun, arity, app, cores, out, tried, fuel, seed_args, cut, have, native_args) do
    args = ["--entry", "#{mod}:#{fun}/#{arity}", "-o", app] ++ native_args ++ seed_args ++ cores
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
        # Even a successful build can name dynamic-dispatch candidates
        # (consolidated protocol impls) that it did not see. Pull the ones
        # that have a beam and rebuild.
        candidates =
          (Regex.scan(~r/dynamic module candidate '([^']+)'/, output) ++
             Regex.scan(~r/module '([^']+)' \(required by .*\) is not among/, output))
          |> Enum.map(fn [_, m] -> m end)
          |> Enum.uniq()
          |> Enum.reject(&(MapSet.member?(tried, &1) or MapSet.member?(have, &1)))

        {pulled, tried, have} = pull_all(candidates, out, cut, tried, have, " (dynamic)")

        if pulled == [] or fuel == 0 do
          # Candidate notes are driver protocol. The regexes above consume
          # them. Missing-module reports that no pull can resolve describe
          # dead call sites. Those abort only if they ever run. Summarize both
          # instead of a full dump on every successful build.
          {missing_lines, rest} =
            output
            |> String.split("\n")
            |> Enum.reject(&String.starts_with?(&1, "manac: note: dynamic module candidate"))
            |> Enum.split_with(&String.starts_with?(&1, "manac: module '"))

          rest |> Enum.join("\n") |> IO.write()

          case missing_lines do
            [] ->
              :ok

            lines ->
              if System.get_env("MANA_DEBUG_LOOP") do
                Enum.each(lines, &IO.puts/1)
              else
                IO.puts(
                  "mana: #{length(lines)} referenced modules are not compiled " <>
                    "(dead call sites — abort if ever reached; MANA_DEBUG_LOOP=1 lists them)"
                )
              end
          end

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
            have,
            native_args
          )
        end

      fuel == 0 ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status}). The dependency chase gave up.")

      (missing =
         missing_modules(output)
         |> Enum.reject(&(MapSet.member?(tried, &1) or MapSet.member?(have, &1)))) != [] ->
        {pulled, tried, have} = pull_all(missing, out, cut, tried, have, "")

        if pulled == [] do
          IO.write(output)
          Mix.raise("manac failed (exit #{status}). See the output above.")
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
          have,
          native_args
        )

      true ->
        IO.write(output)
        Mix.raise("manac failed (exit #{status})")
    end
  end

  # Pull the core of each module plus its whole static import closure (beam
  # ImpT chunks). One chase round then absorbs the whole subgraph instead of
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
        # Toolchain beams (outside the build of this project) go to the shared
        # cache. Project-local beams (consolidated protocols and similar) go
        # to the out dir.
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

        # Build-tool applications never belong in a runtime binary. Their
        # protocol impls (Collectable.Mix.Shell, ...) stay unimplemented.
        # eex is NOT one of them: compiled EEx templates call EEx.Engine
        # at run time (Plug.Debugger error pages).
        if beam =~ ~r{/(mix|ex_unit|iex)(-[\d.]+)?/ebin/} do
          :error
        else
          {:ok, beam}
        end

      _ ->
        :error
    end
  end

  # Core dumps are pure functions of the beam. Skip the dump when the core is
  # newer.
  defp dump_if_stale(beam, core) do
    fresh? =
      case {File.stat(core, time: :posix), File.stat(beam, time: :posix)} do
        {{:ok, %{mtime: c}}, {:ok, %{mtime: b}}} -> c >= b
        _ -> false
      end

    unless fresh?, do: Mana.CoreDump.dump!(beam, core)
  end

  defp core_module(core), do: Path.basename(core, ".core")

  # out/manifest holds the full core list of the last successful build. So a
  # warm rebuild starts complete and compiles in one round. The header is
  # keyed to the toolchain. Core dumps are toolchain-version functions of the
  # beams.
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

  # <user cache>/mana/cores/<elixir>-otp<otp>. Core dumps are pure functions
  # of the beam, so one cache per toolchain serves every project.
  # :filename.basedir obeys the convention of each OS (XDG on Linux,
  # ~/Library/Caches on macOS, Local AppData on Windows). MANA_CACHE_DIR
  # overrides the base. The object cache of manac reads the same variable.
  defp shared_cache_dir do
    base =
      case System.get_env("MANA_CACHE_DIR") do
        nil -> List.to_string(:filename.basedir(:user_cache, ~c"mana"))
        dir -> dir
      end

    Path.join([base, "cores", "#{System.version()}-otp#{System.otp_release()}"])
  end

  # True when the marker is at least as new as every compiled beam. That is,
  # no plain (unscrubbed) compile ran after the last --app build wrote the
  # marker. A newer beam means that a dev compile poisoned the build dir. Then
  # the task must force a scrubbed recompile.
  defp marker_fresh?(marker) do
    case File.stat(marker, time: :posix) do
      {:ok, %{mtime: m}} ->
        Path.wildcard(Path.join(Mix.Project.compile_path(), "*.beam"))
        |> Enum.all?(fn beam ->
          case File.stat(beam, time: :posix) do
            {:ok, %{mtime: b}} -> b <= m
            _ -> false
          end
        end)

      _ ->
        false
    end
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
