defmodule :mana_json_native do
  @moduledoc """
  BEAM-side stub for the native JSON shim. Both functions return
  `{:error, :not_supported_on_beam}`. A misconfigured runtime then fails
  loudly. It does not fail in silence.

  This module loads only under the `:mana` build env. The package is
  `only: [:mana]` in the host app. When mana compiles the host app, the build
  binds `encode/1` and `decode/1` to the symbols in `native/mana_json/`
  (`mana_json_native_encode_1` and `_decode_1`, backed by serde_json). The
  build cuts these stub bodies. On every other env Phoenix uses Jason
  directly (see config/config.exs of the host app). These stubs never run
  there.
  """

  def encode(_term), do: {:error, :not_supported_on_beam}
  def decode(_input), do: {:error, :not_supported_on_beam}
end
