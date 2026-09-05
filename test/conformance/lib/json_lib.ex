defmodule Conf.JSON do
  @moduledoc """
  Runtime pick of the JSON library for the conformance drivers.

  The harness compiles each `Conf.*` beam once and runs it both as a native
  binary and on the BEAM oracle. The choice must therefore happen at
  runtime, not at compile time. On the native binary `:mana_json_native` is
  bound to the serde crate and returns `{:ok, _}`. On the BEAM oracle it is
  the pure stub and returns `{:error, :not_supported_on_beam}`. The probe
  of that result selects `ManaJSON` (native) or `Jason` (oracle).
  """

  @doc "The JSON module for this runtime: ManaJSON on the native binary, Jason on BEAM."
  def lib do
    case :mana_json_native.encode(%{}) do
      {:ok, _} -> ManaJSON
      _ -> Jason
    end
  end
end
