defmodule Conf.Json do
  @moduledoc """
  Native JSON via `ManaJSON` (the mana_json package's Mana.Native binding).
  On mana the encode/decode BIFs run in the package's native crate; on the
  BEAM oracle they delegate to Jason. Encoded *bytes* can differ (key order
  / formatting), so this compares only DECODED structures and roundtrip
  booleans — never raw encoded output.
  """

  def go do
    # fixed blobs decode identically on both runtimes
    IO.puts(inspect(ManaJSON.decode!(~s({"a":1,"b":[true,false,null],"s":"hi"}))))
    IO.puts(inspect(ManaJSON.decode!(~s([1,2.5,-3,"x",{"k":"v"}]))))
    IO.puts(inspect(ManaJSON.decode!(~s({"unicode":"héllo","empty":{},"nil":null}))))

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
      IO.puts(inspect(ManaJSON.decode!(ManaJSON.encode!(x)) == x))
    end

    # a LiveView-diff-shaped payload (the real workload)
    diff = %{"0" => "1", "p" => %{"0" => ["<div>", "</div>"]}, "r" => 1, "s" => 0}
    IO.puts(inspect(ManaJSON.decode!(ManaJSON.encode!(diff)) == diff))

    IO.puts(inspect(:done))
    :ok
  end
end
