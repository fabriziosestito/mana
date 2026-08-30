defmodule Benchmarks.MixProject do
  use Mix.Project

  def project do
    [
      app: :benchmarks,
      version: "0.1.0",
      elixir: "~> 1.14",
      elixirc_options: [debug_info: true],
      deps: [
        {:mana, path: "../hex/mana"},
        {:benchee, "~> 1.1"},
        {:ecto, "~> 3.13"},
      {:bandit, "~> 1.11"}
      ]
    ]
  end
end
