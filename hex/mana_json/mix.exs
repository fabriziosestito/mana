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
          "native BIF backed by serde_json; on BEAM the module delegates to Jason."
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    [
      # Mana.Native macro (a marker) + the build pipeline.
      {:mana, path: "../mana"},
      # BEAM-side fallback for the stub bodies + the conformance oracle.
      {:jason, "~> 1.2"}
    ]
  end
end
