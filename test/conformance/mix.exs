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
        {:ecto, "~> 3.13"},
        # the web stack: bandit pulls thousand_island + plug + friends
        {:bandit, "~> 1.11"},
        # the scaffolded Phoenix app (mix phx.new, landing-page gate)
        {:phx_app, path: "../../examples/phoenix/phx_app"},
        # native JSON (Mana.Native — ships a native/ crate)
        {:mana_json, path: "../../hex/mana_json"}
      ]
    ]
  end
end
