defmodule :mana_json_native do
  @moduledoc """
  BEAM-side stub for the native JSON shim. Both functions return
  `{:error, :not_supported_on_beam}` so a misconfigured runtime fails
  loudly instead of silently doing nothing.

  This module is only ever loaded under the `:mana` build env (the package
  is `only: [:mana]` in the host app). When the host app is compiled with
  mana, the build binds `encode/1` and `decode/1` to the symbols in
  `native/mana_json/` (`mana_json_native_encode_1` / `_decode_1`, backed by
  serde_json) and these stub bodies are cut. On every other env Phoenix
  uses Jason directly (see the host app's config/config.exs), so these
  stubs are never reached.
  """

  def encode(_term), do: {:error, :not_supported_on_beam}
  def decode(_input), do: {:error, :not_supported_on_beam}
end
