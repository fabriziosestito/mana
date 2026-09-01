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

      # subject: compile with mana and run the native binary. The out dir
      # (and its core-cache of dumped stdlib beams, mtime-keyed) survives
      # across runs — a cold stdlib chase costs minutes, a warm one is a
      # single manac invocation. Only the binary must be fresh.
      out_dir = Path.join(System.tmp_dir!(), "mana_conf_#{mod_str}")
      File.rm(Path.join(out_dir, "app"))
      # rerun, not run: run/1 caches per task name and would no-op for the
      # second program in the suite
      Mix.Task.rerun("mana.compile", ["--entry", "#{mod_str}.go/0", "--out", out_dir])
      app = Path.join(out_dir, "app")
      assert File.exists?(app), "manac did not produce #{app}"
      # stdout only — both sides may emit crash reports on stderr
      {native, status} = System.cmd(app, [])
      assert status == 0, "native #{mod_str} crashed (exit #{status}):\n#{native}"

      # oracle: same module, fresh BEAM OS process (all dep ebins on path)
      pa_args =
        Path.wildcard(Path.join(Mix.Project.build_path(), "lib/*/ebin"))
        |> Enum.flat_map(&["-pa", &1])

      {beam_out, 0} = System.cmd("elixir", pa_args ++ ["-e", "#{mod_str}.go()"])

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

  # Release-style boot gate: `mix mana.compile --app` on the scaffolded
  # Phoenix app; the SAME generated Mana.AppBoot module boots the app on
  # both runtimes (native binary vs plain `elixir -pa` — no Mix on either
  # side), and the served landing page facts must agree.
  describe "release-style application boot" do
    @tag timeout: 900_000
    test "phx_app --app serves the landing page identically on both runtimes" do
      phx_dir = Path.expand("../../../examples/phoenix/phx_app", __DIR__)
      manac = System.get_env("MANA_BIN") || raise "MANA_BIN not set"

      {out, status} =
        System.cmd("mix", ["mana.compile", "--app"],
          cd: phx_dir,
          env: [{"MANA_BIN", manac}],
          stderr_to_stdout: true
        )

      assert status == 0, "mana.compile --app failed:\n#{out}"

      native = with_server(:native, phx_dir, &request_facts/1)
      beam = with_server(:beam, phx_dir, &request_facts/1)
      assert native == beam
      assert %{root_status: "HTTP/1.1 200 OK", nope_status: "HTTP/1.1 404 Not Found"} =
               Map.take(native, [:root_status, :nope_status])
    end
  end

  defp request_facts(port) do
    {status, headers, body} = http_get(port, "/")
    {status2, _h2, body2} = http_get(port, "/nope")

    %{
      root_status: status,
      content_type: Map.get(headers, "content-type"),
      framework: String.contains?(body, "Phoenix Framework"),
      csrf: String.contains?(body, "<meta name=\"csrf-token\""),
      cookie: Map.has_key?(headers, "set-cookie"),
      nope_status: status2,
      nope_marker: String.contains?(body2, "NoRouteError")
    }
  end

  defp with_server(kind, phx_dir, fun) do
    port = free_port()

    env = [
      {"PORT", Integer.to_string(port)},
      {"PHX_SERVER", "true"}
    ]

    spawn_args =
      case kind do
        :native ->
          {Path.join(phx_dir, "_mana/app"), []}

        :beam ->
          pa =
            [Path.join(phx_dir, "_mana") | Path.wildcard(Path.join(phx_dir, "_build/dev/lib/*/ebin"))]
            |> Enum.flat_map(&["-pa", &1])

          {System.find_executable("elixir"),
           pa ++ ["-e", ":logger.remove_handler(:default); Mana.AppBoot.start_all(); Process.sleep(:infinity)"]}
      end

    {exe, args} = spawn_args

    os_pid =
      spawn_os(exe, args, env)

    try do
      wait_listening(port, 100)
      fun.(port)
    after
      System.cmd("kill", ["-9", Integer.to_string(os_pid)])
    end
  end

  defp spawn_os(exe, args, env) do
    port =
      Port.open({:spawn_executable, exe}, [
        :binary,
        args: args,
        env:
          Enum.map(env, fn {k, v} -> {String.to_charlist(k), String.to_charlist(v)} end)
      ])

    {:os_pid, os_pid} = Port.info(port, :os_pid)
    os_pid
  end

  defp free_port do
    {:ok, s} = :gen_tcp.listen(0, [])
    {:ok, port} = :inet.port(s)
    :gen_tcp.close(s)
    port
  end

  defp wait_listening(_port, 0), do: raise("server never started listening")

  defp wait_listening(port, tries) do
    case :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}], 200) do
      {:ok, s} ->
        :gen_tcp.close(s)

      {:error, _} ->
        Process.sleep(100)
        wait_listening(port, tries - 1)
    end
  end

  defp http_get(port, path) do
    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    :ok = :gen_tcp.send(c, "GET #{path} HTTP/1.1\r\nhost: t\r\n\r\n")
    {head, leftover} = read_head(c, "")
    [status | header_lines] = String.split(head, "\r\n", trim: true)

    headers =
      header_lines
      |> Enum.map(fn l ->
        [k, v] = String.split(l, ": ", parts: 2)
        {String.downcase(k), v}
      end)
      |> Map.new()

    len = String.to_integer(Map.get(headers, "content-length", "0"))
    body = read_body(c, leftover, len)
    :ok = :gen_tcp.close(c)
    {status, headers, body}
  end

  defp read_head(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, rest] ->
        {head, rest}

      _ ->
        {:ok, chunk} = :gen_tcp.recv(c, 0, 10_000)
        read_head(c, acc <> chunk)
    end
  end

  defp read_body(_c, buf, len) when byte_size(buf) >= len, do: binary_part(buf, 0, len)

  defp read_body(c, buf, len) do
    {:ok, more} = :gen_tcp.recv(c, len - byte_size(buf), 10_000)
    read_body(c, buf <> more, len)
  end
end
