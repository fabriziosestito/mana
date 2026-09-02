defmodule ManaJSON.MixProject do
  use Mix.Project

  @version "0.1.0"

  def project do
    [
      app: :mana_json,
      version: @version,
      elixir: "~> 1.15",
      deps: deps(),
      # Native crate shipped under native/mana_json/. The mana builder
      # (mix mana.compile) discovers this, cargo-builds the crate, and binds
      # :mana_json_native's functions to its symbols. On BEAM this key is
      # ignored and the lib/ stubs (Jason-backed) run instead.
      mana_native: [
        packages: [
          {:mana_json, [module: "mana_json_native"]}
        ]
      ],
      description:
        "Native JSON for apps compiled with mana. encode/decode are a " <>
          "native BIF backed by serde_json; on BEAM the module is a stub and " <>
          "the host app uses Jason directly (config_env() switch)."
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    # No deps: the package ships the native crate under native/mana_json/ and
    # a pure BEAM stub. It never references Jason — the host app selects Jason
    # vs ManaJSON in its own config (config_env() == :mana).
    []
  end
end
