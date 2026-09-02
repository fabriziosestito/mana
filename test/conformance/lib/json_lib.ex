defmodule Conf.JSON do
  @moduledoc """
  Runtime pick of the JSON library for the conformance drivers.

  The harness compiles each `Conf.*` beam once and runs it both as a native
  binary and on the BEAM oracle, so the choice must be made at runtime, not
  at compile time. On the native binary `:mana_json_native` is bound to the
  serde crate and returns `{:ok, _}`; on the BEAM oracle it is the pure stub
  returning `{:error, :not_supported_on_beam}`. Probe that to select
  `ManaJSON` (native) vs `Jason` (oracle).
  """

  @doc "The JSON module to use on this runtime: ManaJSON natively, Jason on BEAM."
  def lib do
    case :mana_json_native.encode(%{}) do
      {:ok, _} -> ManaJSON
      _ -> Jason
    end
  end
end
