defmodule Mana.MixProject do
  use Mix.Project

  def project do
    [
      app: :mana,
      version: "0.1.0",
      elixir: "~> 1.14",
      deps: [],
      description:
        "Compile Elixir to native binaries via mana (Core Erlang → LLVM). " <>
          "Adds the `mix mana.compile` task that runs the `manac` compiler " <>
          "on this project's BEAM files.",
      package: package()
    ]
  end

  def application do
    [extra_applications: []]
  end

  defp package do
    [
      licenses: ["Apache-2.0"],
      links: %{"GitHub" => "https://github.com/fabriziosestito/mana"}
    ]
  end
end
