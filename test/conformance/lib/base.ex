defmodule Conf.Base do
  @moduledoc """
  Elixir.Base encode/decode 64 (std + url) and 16 — natively overridden on
  mana (Base is a compiled clause-table codec; url_encode64 alone was ~13%
  of a Phoenix request). Pins padding / ignore-whitespace / case rules and
  the error shapes against the BEAM oracle.
  """

  def go do
    for data <- ["", "a", "ab", "abc", "abcd", <<251, 255, 254>>, <<0, 1, 2, 3, 4, 5, 6, 7>>,
                 :crypto.hash(:sha256, "seed"), String.duplicate("xyz", 40)] do
      IO.puts(Base.encode64(data))
      IO.puts(Base.encode64(data, padding: false))
      IO.puts(Base.url_encode64(data))
      IO.puts(Base.url_encode64(data, padding: false))
      IO.puts(Base.encode16(data))
      IO.puts(Base.encode16(data, case: :lower))
      IO.puts(Base.encode16(data, case: :upper))
      # roundtrips
      IO.puts(inspect(Base.decode64(Base.encode64(data)) == {:ok, data}))
      IO.puts(inspect(Base.decode64(Base.encode64(data, padding: false), padding: false) == {:ok, data}))
      IO.puts(inspect(Base.url_decode64(Base.url_encode64(data)) == {:ok, data}))
      IO.puts(inspect(Base.url_decode64(Base.url_encode64(data, padding: false), padding: false) == {:ok, data}))
      IO.puts(inspect(Base.decode16(Base.encode16(data)) == {:ok, data}))
      IO.puts(inspect(Base.decode16(Base.encode16(data, case: :lower), case: :lower) == {:ok, data}))
      IO.puts(inspect(Base.decode16(Base.encode16(data), case: :mixed) == {:ok, data}))
    end

    # decode64 edge matrix (both padding modes, with/without whitespace)
    inputs = [
      "YWI=", "YWI", "YW==", "YW=", "YQ==", "YQ=", "YR==", "Y", "", "YWI=x", "=", "==", "====",
      "YW I=", "YW I=\n", "YW\tI=", "\r\nYWI=", "YW\x0bI=", "YWJj", "YWJjZA==", "YWJjZA",
      "-__-", "+__+", "YWI=YWI=", "Y W I", "YWI==", "YWI="
    ]

    for s <- inputs do
      IO.puts(
        "#{inspect(s)}: " <>
          inspect({
            Base.decode64(s),
            Base.decode64(s, padding: false),
            Base.decode64(s, ignore: :whitespace),
            Base.decode64(s, padding: false, ignore: :whitespace),
            Base.url_decode64(s),
            Base.url_decode64(s, padding: false)
          })
      )
    end

    for s <- ["617A", "617a", "617", "61 7A", "", "ZZ", "0a", "0A", "617Az"] do
      IO.puts(
        "#{inspect(s)}: " <>
          inspect({
            Base.decode16(s),
            Base.decode16(s, case: :lower),
            Base.decode16(s, case: :upper),
            Base.decode16(s, case: :mixed)
          })
      )
    end

    # bad arguments raise the same exception on both runtimes
    for f <- [
          fn -> Base.encode64(:x) end,
          fn -> Base.encode64("a", foo: 1) end,
          fn -> Base.encode64("a", padding: 1) end,
          fn -> Base.decode64("YQ==", ignore: :all) end,
          fn -> Base.encode16("a", case: :mixed) end,
          fn -> Base.decode16(123) end,
          fn -> Base.url_decode64("a", [:padding]) end
        ] do
      r =
        try do
          {:ok, f.()}
        rescue
          e -> {:raised, e.__struct__}
        end

      IO.puts(inspect(r))
    end

    IO.puts(inspect(:done))
    :ok
  end
end
