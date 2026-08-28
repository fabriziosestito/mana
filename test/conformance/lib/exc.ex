defmodule Conf.Exc do
  @moduledoc """
  Conformance program: exceptions — throw/exit/error caught, nested try,
  re-raise on unmatched catch clauses, cross-function failures, badfun,
  case_clause, after blocks. Uses Elixir's `catch class, reason` form only
  (rescue needs Exception structs, i.e. maps/stdlib we don't support yet).
  """

  def go do
    # the three classes, caught
    :erlang.display(catcher(fn -> :erlang.throw(:ball) end))
    :erlang.display(catcher(fn -> :erlang.exit(:normal_ish) end))
    :erlang.display(catcher(fn -> :erlang.error(:boom) end))

    # no exception: body value flows through
    :erlang.display(catcher(fn -> 42 end))

    # reasons carrying heap data survive the catch (GC scans eternal refs)
    :erlang.display(catcher(fn -> :erlang.throw({:data, [1, 2, 3]}) end))

    # nested: inner catches only :specific, others pass to the outer
    :erlang.display(nested(:specific))
    :erlang.display(nested(:other))

    # failures raised by the machine, not by user code
    :erlang.display(catcher(fn -> one_only(2) end))
    :erlang.display(catcher(fn -> case 7 do 1 -> :one end end))
    :erlang.display(catcher(fn -> not_a_fun() end))

    # after runs on both paths
    :erlang.display(with_after(fn -> :fine end))
    :erlang.display(with_after(fn -> :erlang.throw(:oops) end))
  end

  defp catcher(f) do
    try do
      f.()
    catch
      class, reason -> {:caught, class, reason}
    end
  end

  defp nested(x) do
    try do
      try do
        :erlang.throw(x)
      catch
        :throw, :specific -> :inner_got_it
      end
    catch
      class, reason -> {:outer, class, reason}
    end
  end

  defp one_only(1), do: :one

  defp not_a_fun do
    f = 17
    f.(1)
  end

  defp with_after(f) do
    try do
      try do
        f.()
      after
        :erlang.display(:after_ran)
      end
    catch
      class, reason -> {:after_caught, class, reason}
    end
  end
end
