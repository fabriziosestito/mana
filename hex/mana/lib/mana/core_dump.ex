defmodule Mana.CoreDump do
  @moduledoc """
  Extracts textual Core Erlang from a compiled `.beam` file.

  Reads the `debug_info` chunk (the project must be compiled with
  `debug_info: true`, which is Mix's default outside `:prod`), asks the
  compiler backend for the Core Erlang form, and pretty-prints it with
  `:core_pp` — the same textual format `erlc +to_core` emits, which is
  what `manac` parses.
  """

  def dump!(beam_path, out_path) do
    case :beam_lib.chunks(String.to_charlist(beam_path), [:debug_info]) do
      {:ok, {_module, [{:debug_info, {:debug_info_v1, backend, data}}]}} ->
        case backend.debug_info(:core_v1, :elixir, data, []) do
          {:ok, core} ->
            File.write!(out_path, :core_pp.format(core))
            :ok

          {:error, reason} ->
            Mix.raise("could not get Core Erlang from #{beam_path}: #{inspect(reason)}")
        end

      {:ok, {_module, [{:debug_info, :no_debug_info}]}} ->
        Mix.raise("""
        #{beam_path} was compiled without debug_info.

        Ensure your project does not disable it, e.g. in mix.exs:

            elixirc_options: [debug_info: true]
        """)

      {:error, :beam_lib, reason} ->
        Mix.raise("could not read #{beam_path}: #{inspect(reason)}")
    end
  end
end
