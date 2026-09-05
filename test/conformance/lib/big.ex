defmodule Conf.Big do
  @moduledoc """
  Bignums against the BEAM oracle. The program checks overflow promotion
  and demotion at every ±2^60 boundary, decimal printing, and exact
  comparisons (also against floats and as map keys). It also checks bit ops
  and shifts across the boundary, and a factorial loop that stresses
  shared-old-space allocation.
  """

  @small_max 1_152_921_504_606_846_975
  @small_min -1_152_921_504_606_846_976

  def go do
    # Promotion at the boundaries. Every arm must round-trip through BEAM.
    :erlang.display(@small_max + 1)
    :erlang.display(@small_min - 1)
    :erlang.display(-@small_min)
    :erlang.display(abs(@small_min))
    :erlang.display(div(@small_min, -1))
    :erlang.display(@small_max * 2)
    :erlang.display(@small_min * 2)
    :erlang.display(1_073_741_824 * 1_073_741_824)

    # Demotion: big - big is small again.
    big = @small_max + 10
    :erlang.display(big - 20)
    :erlang.display(big - big)
    :erlang.display(is_integer(big) and is_number(big))

    # Big literals and arithmetic on them.
    huge = 123_456_789_012_345_678_901_234_567_890
    :erlang.display(huge)
    :erlang.display(huge + 1)
    :erlang.display(huge * huge)
    :erlang.display(div(huge, 1_000_000_000))
    :erlang.display(rem(huge, 97))
    :erlang.display(-huge)
    :erlang.display(huge - huge)

    # div/rem sign matrix. div truncates, and rem takes the dividend sign.
    :erlang.display({div(-huge, 7), rem(-huge, 7)})
    :erlang.display({div(huge, -7), rem(huge, -7)})

    # Comparison matrix: exact int/int, int/float, ordering, and map keys.
    :erlang.display(huge > @small_max)
    :erlang.display(-huge < @small_min)
    :erlang.display(huge == huge + 0)
    :erlang.display(huge === huge)
    :erlang.display(9_007_199_254_740_993 == 9_007_199_254_740_992)
    :erlang.display(min(huge, 5))
    m = %{huge => :big, (huge + 1) => :bigger, 5 => :small}
    :erlang.display(map_size(m))
    :erlang.display(Map.get(m, huge))
    :erlang.display(Enum.sort(Map.keys(m)))

    # shifts and bit ops across the boundary
    :erlang.display(Bitwise.bsl(1, 100))
    :erlang.display(Bitwise.bsr(Bitwise.bsl(1, 100), 100))
    :erlang.display(Bitwise.bsl(-1, 65))
    :erlang.display(Bitwise.bsr(-1024, 3))
    :erlang.display(Bitwise.bsr(Bitwise.bsl(-3, 80), 79))
    :erlang.display(Bitwise.band(Bitwise.bsl(1, 100) + 255, 255))
    :erlang.display(Bitwise.bor(Bitwise.bsl(1, 70), 1))
    :erlang.display(Bitwise.bxor(Bitwise.bsl(1, 70), Bitwise.bsl(1, 70)))
    :erlang.display(Bitwise.bnot(Bitwise.bsl(1, 90)))

    # to_string/inspect path
    :erlang.display(Integer.to_string(huge) == "123456789012345678901234567890")

    # Factorial: promotion, big×small multiplication, and old-space churn.
    :erlang.display(fact(50))
    :erlang.display(rem(fact(200), 1_000_000_007))
    :erlang.display(byte_size(Integer.to_string(fact(200))))

    # float boundary
    :erlang.display(1.0e18 < huge)
    :erlang.display(huge * 1.0 > 1.0e29)

    # ETF round-trips at and past one limb
    two64 = Bitwise.bsl(1, 64)
    for v <- [two64, -two64, huge, -huge, Bitwise.bsl(1, 200), @small_max + 1] do
      :erlang.display(:erlang.binary_to_term(:erlang.term_to_binary(v)) == v)
    end

    :erlang.display(:binary.decode_unsigned(<<255, 255, 255, 255, 255, 255, 255, 255, 255>>))
    :erlang.display(:binary.decode_unsigned(:binary.copy(<<170>>, 16), :little))

    # Float to integer beyond the small range.
    :erlang.display(trunc(1.0e30))
    :erlang.display(round(-1.0e25))
    :erlang.display(:erlang.float(huge) == 1.2345678901234568e29)

    # Time: true Unix epoch. The values are nondeterministic, so only facts print.
    secs = :os.system_time(:second)
    ns = :os.system_time(:nanosecond)
    :erlang.display(secs > 1_700_000_000 and secs < 2_000_000_000)
    :erlang.display(ns > Bitwise.bsl(1, 60))
    back = :erlang.convert_time_unit(ns, :nanosecond, :second)
    :erlang.display(abs(back - secs) <= 2)

    :erlang.display(:done)
    :ok
  end

  defp fact(0), do: 1
  defp fact(n), do: n * fact(n - 1)
end
