defmodule :mana_json_native do
  @moduledoc """
  The native-bound JSON BIFs. This package's `mana_native:` mix metadata
  (see mix.exs) tells the mana build to bind `encode/1` and `decode/1` to
  the symbols in `native/mana_json/` (`mana_json_native_encode_1` /
  `_decode_1`).

  On BEAM the bodies below run as ordinary Elixir — they delegate to Jason
  so a normal Elixir run and the conformance oracle behave the same as the
  native path. When compiled with mana, these bodies are cut and never
  reached.

  (A `use Mana.Native` marker exists for documentation, but is intentionally
  not used here to avoid a compile-time dependency on the mana package — the
  build discovers this module solely through the `mana_native:` mix key.)
  """

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
