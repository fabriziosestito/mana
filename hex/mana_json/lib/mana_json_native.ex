defmodule :mana_json_native do
  @moduledoc """
  The native-bound JSON BIFs. Declared with `use Mana.Native` so the mana
  build recognizes it (from this package's `mana_native:` mix metadata) and
  binds `encode/1` and `decode/1` to the symbols in `native/mana_json/`.

  On BEAM the bodies below run as ordinary Elixir — they delegate to Jason
  so a normal Elixir run and the conformance oracle behave the same as the
  native path. When compiled with mana, these bodies are cut and never
  reached; the native crate's `mana_json_native_encode_1` / `_decode_1`
  handle the call instead.
  """

  use Mana.Native, otp_app: :mana_json, package: :mana_json

  def encode(term) do
    {:ok, IO.iodata_to_binary(Jason.encode_to_iodata!(term))}
  rescue
    e -> {:error, Exception.message(e)}
  end

  def decode(input) do
    {:ok, Jason.decode!(input)}
  rescue
    e -> {:error, Exception.message(e)}
  end
end
