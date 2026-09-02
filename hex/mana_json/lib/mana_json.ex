defmodule ManaJSON do
  @moduledoc """
  JSON library shim for apps compiled with mana. Implements the small
  subset of the Jason API that Phoenix and Plug.Parsers call —
  `encode!/1`, `encode_to_iodata!/1`, `decode!/1` (plus non-raising
  `encode/1` / `decode/1`) — by forwarding to `:mana_json_native`.

  Wire it up as Phoenix's `:json_library`, only under the mana build:

      config :phoenix, :json_library,
        if(config_env() == :mana, do: ManaJSON, else: Jason)

  When the app is compiled with mana, the build binds `:mana_json_native`'s
  functions to the native BIFs shipped in this package's `native/mana_json/`
  crate. On BEAM this module is not used (the package is `only: [:mana]` and
  Phoenix uses Jason directly); the `:mana_json_native` stub only returns
  `{:error, :not_supported_on_beam}` as a loud safety net.
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
