defmodule ConformanceTest do
  @moduledoc """
  BEAM is the oracle: every `Conf.*` module under lib/ with a `go/0` is run
  once on BEAM (as a separate OS process — `:erlang.display/1` bypasses the
  group leader, so `capture_io` can't see it) and once as a mana-compiled
  native binary. The two stdouts must match. No golden files.
  """

  use ExUnit.Case, async: false

  # stdlib programs chase and compile ~200 beams on a cold cache
  @moduletag timeout: 900_000

  # Discover Conf.* modules at compile time; lib/ is compiled before tests.
  programs =
    Mix.Project.compile_path()
    |> Path.join("Elixir.Conf.*.beam")
    |> Path.wildcard()
    |> Enum.map(&(&1 |> Path.basename(".beam") |> String.trim_leading("Elixir.")))
    |> Enum.sort()
    |> Enum.filter(fn mod_str ->
      mod = Module.concat([mod_str])
      Code.ensure_loaded?(mod) and function_exported?(mod, :go, 0)
    end)

  if programs == [] do
    raise "no Conf.* programs with go/0 found — conformance suite is empty"
  end

  for mod_str <- programs do
    @mod_str mod_str
    @tag program: mod_str
    test "#{mod_str} native output matches BEAM" do
      mod_str = @mod_str

      # subject: compile with mana and run the native binary
      out_dir = Path.join(System.tmp_dir!(), "mana_conf_#{mod_str}")
      File.rm_rf!(out_dir)
      # rerun, not run: run/1 caches per task name and would no-op for the
      # second program in the suite
      Mix.Task.rerun("mana.compile", ["--entry", "#{mod_str}.go/0", "--out", out_dir])
      app = Path.join(out_dir, "app")
      assert File.exists?(app), "manac did not produce #{app}"
      # stdout only — both sides may emit crash reports on stderr
      {native, status} = System.cmd(app, [])
      assert status == 0, "native #{mod_str} crashed (exit #{status}):\n#{native}"

      # oracle: same module, fresh BEAM OS process
      {beam_out, 0} =
        System.cmd("elixir", ["-pa", Mix.Project.compile_path(), "-e", "#{mod_str}.go()"])

      assert normalize(native) == normalize(beam_out),
             "output diverges from BEAM for #{mod_str}"
    end
  end

  defp normalize(s) do
    s
    |> String.split("\n")
    |> Enum.map(&String.trim_trailing/1)
    |> Enum.join("\n")
    |> String.trim_trailing()
  end
end
