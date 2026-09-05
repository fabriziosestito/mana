defmodule ManaJSON.MixProject do
  use Mix.Project

  @version "0.1.0"

  def project do
    [
      app: :mana_json,
      version: @version,
      elixir: "~> 1.15",
      deps: deps(),
      # The native crate is under native/mana_json/. The mana builder
      # (mix mana.compile) finds this key, builds the crate with cargo, and
      # binds the functions of :mana_json_native to its symbols. On BEAM this
      # key is ignored and the stubs under lib/ run instead.
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
    # No deps. The package ships the native crate under native/mana_json/ and
    # a pure BEAM stub. It never references Jason. The host app selects Jason
    # or ManaJSON in its own config (config_env() == :mana).
    []
  end
end
