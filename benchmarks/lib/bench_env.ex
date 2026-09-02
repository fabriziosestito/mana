defmodule Bench.Env do
  @moduledoc """
  Runtime picks for the benchmark drivers. The same beam runs natively and on
  BEAM, so native-only packages are selected by probing their bindings at
  runtime rather than by compile-time config.
  """

  @doc "JSON library: ManaJSON on the native binary (serde), Jason on BEAM."
  def json_library do
    case :mana_json_native.encode(%{}) do
      {:ok, _} -> ManaJSON
      _ -> Jason
    end
  end

  @doc "Phoenix endpoint adapter: ManaHTTP natively when available, else Bandit."
  def http_adapter do
    if native_http?(), do: ManaHTTP.PhoenixAdapter, else: Bandit.PhoenixAdapter
  end

  @doc "True when the mana_http native binding is present (native binary)."
  def native_http? do
    Code.ensure_loaded?(:mana_http_native) and
      function_exported?(:mana_http_native, :probe, 0) and
      :mana_http_native.probe() == :ok
  end

  @doc "Human-readable runtime tag for report headers."
  def tag do
    sched = System.get_env("MANA_SCHEDULERS", "1")
    "json=#{inspect(json_library())} http=#{inspect(http_adapter())} schedulers=#{sched}"
  end
end
