defmodule Bench.Str do
  @moduledoc "String-heavy paths (unicode tables, binary churn)."

  @text "The quick brown fox, jumps over: the lazy dog! " |> String.duplicate(20)

  def run do
    Benchee.run(
      %{
        "split+join" => fn -> @text |> String.split(" ") |> Enum.join("_") end,
        "upcase" => fn -> String.upcase(@text) end,
        "replace" => fn -> String.replace(@text, "the", "a") end,
        "to_integer round-trip" => fn ->
          1..50 |> Enum.map(&(&1 |> Integer.to_string() |> String.to_integer())) |> Enum.sum()
        end
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end
end
