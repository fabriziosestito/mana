defmodule Conf.Json do
  @moduledoc """
  Native JSON through `ManaJSON`, the Mana.Native binding of the mana_json
  package. On mana the encode and decode BIFs run in the native crate of the
  package. On the BEAM oracle `ManaJSON` cannot run, and the stub returns
  an error, so the oracle uses Jason instead (see `Conf.JSON.lib/0`).
  Encoded *bytes* can differ in key order and formatting. This program
  compares only DECODED structures and roundtrip booleans, never raw
  encoded output.
  """

  def go do
    json = Conf.JSON.lib()

    # Fixed blobs decode identically on both runtimes.
    IO.puts(inspect(json.decode!(~s({"a":1,"b":[true,false,null],"s":"hi"}))))
    IO.puts(inspect(json.decode!(~s([1,2.5,-3,"x",{"k":"v"}]))))
    IO.puts(inspect(json.decode!(~s({"unicode":"héllo","empty":{},"nil":null}))))

    # roundtrips: decode(encode(x)) == x
    inputs = [
      %{"k" => "v", "n" => 42, "list" => [1, 2, 3]},
      [true, false, nil, "str", 3.14, -17],
      %{"nested" => %{"a" => [1, %{"b" => 2}]}},
      "plain string",
      12_345,
      -6789,
      %{},
      []
    ]

    for x <- inputs do
      IO.puts(inspect(json.decode!(json.encode!(x)) == x))
    end

    # A LiveView-diff-shaped payload, the real workload.
    diff = %{"0" => "1", "p" => %{"0" => ["<div>", "</div>"]}, "r" => 1, "s" => 0}
    IO.puts(inspect(json.decode!(json.encode!(diff)) == diff))

    IO.puts(inspect(:done))
    :ok
  end
end
