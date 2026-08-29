defmodule Conf.Regex do
  @moduledoc """
  Conformance program: Regex through the :re cut (Rust regex crate;
  version mismatch forces recompilation from source). No backreferences
  or lookaround — crate limitation, avoided here by construction.
  """

  def go do
    r = ~r/h(a+)llo/
    :erlang.display(Regex.match?(r, "haaallo world"))
    :erlang.display(Regex.match?(r, "hello"))
    :erlang.display(Regex.run(r, "xx haallo yy"))
    :erlang.display(Regex.run(r, "xx haallo yy", return: :index))
    :erlang.display(Regex.run(r, "nope"))

    # flags
    :erlang.display(Regex.match?(~r/HeLLo/i, "hello"))
    :erlang.display(Regex.run(~r/^b.c$/m, "abc\nbxc\n"))
    :erlang.display(Regex.match?(~r/a.c/s, "a\nc"))

    # scan (global)
    :erlang.display(Regex.scan(~r/\d+/, "a1 b22 c333"))
    :erlang.display(Regex.scan(~r/(\w)(\d)/, "a1 b2"))
    :erlang.display(Regex.scan(~r/x/, "none"))

    # replace / split
    :erlang.display(Regex.replace(~r/\d+/, "a1 b22", "N"))
    :erlang.display(Regex.replace(~r/(a)(b)/, "ab ab", "\\2\\1"))
    :erlang.display(Regex.split(~r/,\s*/, "a, b,c"))
    :erlang.display(Regex.split(~r/\d/, "a1b2c", include_captures: true))

    # named captures
    nr = ~r/(?P<year>\d{4})-(?P<month>\d{2})/
    :erlang.display(Regex.names(nr) |> Enum.sort())
    :erlang.display(Regex.named_captures(nr, "on 2024-05 we"))
    :erlang.display(Regex.run(nr, "2024-05", capture: [:month]))

    # anchors / classes (validate_format shapes)
    :erlang.display(Regex.match?(~r/^[a-z0-9._%+-]+@[a-z0-9.-]+$/, "me@example.com"))
    :erlang.display(Regex.match?(~r/^[a-z0-9._%+-]+@[a-z0-9.-]+$/, "not an email"))

    # compile from string + error path
    {:ok, rc} = Regex.compile("^ab+c")
    :erlang.display(Regex.match?(rc, "abbbc"))
    :erlang.display(match?({:error, _}, Regex.compile("(unclosed")))

    # unicode
    :erlang.display(Regex.match?(~r/héllo/u, "well héllo"))
    :erlang.display(Regex.scan(~r/./u, "héo"))

    # under load (interning + GC)
    :erlang.display(churn(200, 0))
  end

  defp churn(0, acc), do: acc

  defp churn(n, acc) do
    s = "item#{n} v#{n * 2}"
    [[_, v]] = Regex.scan(~r/v(\d+)/, s)
    churn(n - 1, acc + String.to_integer(v) - n * 2 + if(Regex.match?(~r/item/, s), do: 1, else: 0))
  end
end
