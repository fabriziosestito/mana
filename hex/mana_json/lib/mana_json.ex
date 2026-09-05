defmodule ManaJSON do
  @moduledoc """
  JSON library shim for apps that mana compiles. This module implements the
  small subset of the Jason API that Phoenix and Plug.Parsers call:
  `encode!/1`, `encode_to_iodata!/1`, `decode!/1`, and the non-raising
  `encode/1` and `decode/1`. Each function forwards to `:mana_json_native`.

  Set this module as the `:json_library` of Phoenix, only under the mana build:

      config :phoenix, :json_library,
        if(config_env() == :mana, do: ManaJSON, else: Jason)

  When mana compiles the app, the build binds the functions of
  `:mana_json_native` to the native BIFs in the `native/mana_json/` crate of
  this package. On BEAM this module is not used. The package is `only: [:mana]`
  and Phoenix uses Jason directly. The `:mana_json_native` stub only returns
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
