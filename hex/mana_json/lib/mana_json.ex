defmodule ManaJSON do
  @moduledoc """
  JSON library shim for apps compiled with mana. Implements the small
  subset of the Jason API that Phoenix and Plug.Parsers call —
  `encode!/1`, `encode_to_iodata!/1`, `decode!/1` (plus non-raising
  `encode/1` / `decode/1`) — by forwarding to `:mana_json_native`.

  Wire it up as Phoenix's `:json_library`:

      config :phoenix, :json_library, ManaJSON

  On BEAM the `:mana_json_native` module delegates to Jason (so a normal
  Elixir run — and the conformance oracle — works). When the app is
  compiled with mana, the build binds those functions to the Go/Rust-free
  native BIFs shipped in this package's `native/mana_json/` crate.
  """

  def encode(term), do: :mana_json_native.encode(term)

  def encode!(term) do
    case :mana_json_native.encode(term) do
      {:ok, bin} -> bin
      {:error, reason} -> raise ArgumentError, "encode failed: #{inspect(reason)}"
    end
  end

  def encode_to_iodata!(term), do: encode!(term)

  def decode(input) when is_binary(input), do: :mana_json_native.decode(input)
  def decode(input) when is_list(input), do: decode(IO.iodata_to_binary(input))

  def decode!(input) do
    case decode(input) do
      {:ok, term} -> term
      {:error, reason} -> raise ArgumentError, "decode failed: #{inspect(reason)}"
    end
  end
end
