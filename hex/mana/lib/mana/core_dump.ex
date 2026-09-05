defmodule Mana.CoreDump do
  @moduledoc """
  This module extracts textual Core Erlang from a compiled `.beam` file.

  It reads the `debug_info` chunk. The project must be compiled with
  `debug_info: true`. This is the Mix default outside `:prod`. The module asks
  the compiler backend for the Core Erlang form and pretty-prints it with
  `:core_pp`. The result is the same textual format that `erlc +to_core`
  emits. `manac` parses this format.
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
