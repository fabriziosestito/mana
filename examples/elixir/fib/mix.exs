defmodule Fib.MixProject do
  use Mix.Project

  def project do
    [
      app: :fib,
      version: "0.1.0",
      elixir: "~> 1.14",
      elixirc_options: [debug_info: true],
      deps: [
        {:mana, path: "../../../hex/mana"}
      ]
    ]
  end
end
