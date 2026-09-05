defmodule Mana do
  @moduledoc """
  This module finds the `manac` compiler binary for `mix mana.compile`.

  Resolution order:

    1. the `:bin` option (`mix mana.compile --bin PATH`)
    2. `config :mana, :bin, "PATH"`
    3. the `MANA_BIN` environment variable
    4. `manac` on `PATH`
  """

  def compiler_path(opts \\ []) do
    cond do
      bin = opts[:bin] -> ensure_exists!(bin)
      bin = Application.get_env(:mana, :bin) -> ensure_exists!(bin)
      bin = System.get_env("MANA_BIN") -> ensure_exists!(bin)
      bin = System.find_executable("manac") -> bin
      true -> raise_not_found!()
    end
  end

  defp ensure_exists!(bin) do
    path = Path.expand(bin)

    if File.exists?(path) do
      path
    else
      Mix.raise("manac binary not found at #{path}")
    end
  end

  defp raise_not_found!() do
    Mix.raise("""
    could not find the manac compiler. Either:

      * pass --bin /path/to/manac
      * set `config :mana, :bin, "/path/to/manac"`
      * export MANA_BIN=/path/to/manac
      * put `manac` on your PATH
    """)
  end
end
