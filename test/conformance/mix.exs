defmodule ManaConformance.MixProject do
  use Mix.Project

  def project do
    [
      app: :mana_conformance,
      version: "0.1.0",
      elixir: "~> 1.14",
      elixirc_options: [debug_info: true],
      deps: [
        {:mana, path: "../../hex/mana"},
        # the pure Ecto layer (schema/changeset/type) — no adapters
        {:ecto, "~> 3.13"}
      ]
    ]
  end
end
