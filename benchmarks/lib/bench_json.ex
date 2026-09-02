defmodule Bench.Json do
  @moduledoc """
  Native JSON (ManaJSON, backed by serde_json) vs compiled-from-source
  Jason, on a LiveView-diff-shaped payload and a larger nested one.

  ManaJSON can only run in a mana-compiled binary (on BEAM the stub errors),
  so the ManaJSON arms are included only when native. On BEAM the bench runs
  the Jason arms alone.
  """

  @diff %{"0" => "1", "p" => %{"0" => ["<div>\n  <h1>Count: <span>", "</span></h1>"]}, "r" => 1, "s" => 0}

  @big for i <- 1..50,
           into: %{},
           do:
             {"key#{i}",
              %{"n" => i, "f" => i * 1.5, "list" => Enum.to_list(1..10), "s" => "value #{i}"}}

  # ManaJSON runs only on the native binary (serde); on BEAM the stub errors.
  defp mana? do
    case :mana_json_native.encode(%{}) do
      {:ok, _} -> true
      _ -> false
    end
  end

  def run do
    diff_json = Jason.encode_to_iodata!(@diff) |> IO.iodata_to_binary()
    big_json = Jason.encode_to_iodata!(@big) |> IO.iodata_to_binary()

    jason_jobs = %{
      "jason encode diff" => fn -> Jason.encode_to_iodata!(@diff) end,
      "jason decode diff" => fn -> Jason.decode!(diff_json) end,
      "jason encode big" => fn -> Jason.encode_to_iodata!(@big) end,
      "jason decode big" => fn -> Jason.decode!(big_json) end
    }

    mana_jobs =
      if mana?() do
        %{
          "mana encode diff" => fn -> ManaJSON.encode_to_iodata!(@diff) end,
          "mana decode diff" => fn -> ManaJSON.decode!(diff_json) end,
          "mana encode big" => fn -> ManaJSON.encode_to_iodata!(@big) end,
          "mana decode big" => fn -> ManaJSON.decode!(big_json) end
        }
      else
        %{}
      end

    Benchee.run(
      Map.merge(jason_jobs, mana_jobs),
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end
end
