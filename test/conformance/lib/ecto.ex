defmodule Conf.Ecto.User do
  use Ecto.Schema
  import Ecto.Changeset

  embedded_schema do
    field :name, :string
    field :email, :string
    field :age, :integer
    field :score, :float
    field :active, :boolean, default: true
  end

  def changeset(user, attrs) do
    user
    |> cast(attrs, [:name, :email, :age, :score, :active])
    |> validate_required([:name, :email])
    |> validate_number(:age, greater_than: 0, less_than: 150)
    |> validate_format(:email, ~r/^[^\s]+@[^\s]+$/, message: "bad email")
    |> validate_length(:name, min: 2, max: 40)
    |> validate_inclusion(:active, [true, false])
  end
end

defmodule Conf.Ecto do
  @moduledoc """
  Conformance program: Ecto's pure layer compiled from hex beams —
  embedded schema, changeset cast/validate (happy and bad paths),
  apply_changes, traverse_errors, and Ecto.Type casts. Maps printed via
  sorted views (flatmap display order is implementation-defined).
  """
  import Ecto.Changeset
  alias Conf.Ecto.User

  def go do
    # happy path
    good = %{"name" => "Ada", "email" => "ada@example.com", "age" => 36, "score" => 9.5}
    cs = User.changeset(%User{}, good)
    :erlang.display(cs.valid?)
    dump_kw(:changes, Enum.sort(Map.to_list(cs.changes)))
    :erlang.display(cs.errors)
    u = apply_changes(cs)
    :erlang.display({u.name, u.email, u.age, u.score, u.active})

    # string keys vs atom keys, defaults, partial updates
    cs2 = User.changeset(u, %{"age" => 37})
    :erlang.display({cs2.valid?, Enum.sort(Map.to_list(cs2.changes))})

    # bad inputs: missing required, out-of-range, bad format, bad length
    bad = %{"name" => "A", "age" => 200, "email" => "nope"}
    cs3 = User.changeset(%User{}, bad)
    :erlang.display(cs3.valid?)
    dump_kw(:errors, Enum.sort(cs3.errors))

    # cast type errors
    cs4 = User.changeset(%User{}, %{"name" => "Bob", "email" => "b@c.d", "age" => "not_int"})
    :erlang.display(cs4.valid?)
    dump_kw(:errors4, Enum.sort(cs4.errors))

    # traverse_errors (message interpolation)
    msgs =
      traverse_errors(cs3, fn {msg, opts} ->
        Enum.reduce(opts, msg, fn {key, value}, acc ->
          String.replace(acc, "%{#{key}}", to_string(value))
        end)
      end)

    dump_kw(:msgs, Enum.sort(Map.to_list(msgs)))

    # more validators / change tracking
    cs5 =
      %User{}
      |> cast(%{"name" => "Eve", "email" => "e@f.g"}, [:name, :email])
      |> put_change(:age, 30)
      |> update_change(:age, &(&1 + 1))
    :erlang.display({get_change(cs5, :age), get_field(cs5, :active)})
    :erlang.display(fetch_change(cs5, :age))
    :erlang.display(fetch_field(cs5, :name))

    # Ecto.Type casts (the runtime workhorse)
    :erlang.display(Ecto.Type.cast(:integer, "42"))
    :erlang.display(Ecto.Type.cast(:integer, 42))
    :erlang.display(Ecto.Type.cast(:integer, "nope"))
    :erlang.display(Ecto.Type.cast(:float, "2.5"))
    :erlang.display(Ecto.Type.cast(:float, 3))
    :erlang.display(Ecto.Type.cast(:boolean, "true"))
    :erlang.display(Ecto.Type.cast(:boolean, "0"))
    :erlang.display(Ecto.Type.cast(:string, "hi"))
    :erlang.display(Ecto.Type.cast({:array, :integer}, ["1", 2]))
    # decimals are structs (maps): display sorted (flatmap-order rule)
    {:ok, d1} = Ecto.Type.cast(:decimal, "1.5")
    :erlang.display({:ok, Enum.sort(Map.to_list(d1))})
    {:ok, d2} = Ecto.Type.cast(:decimal, 7)
    :erlang.display({:ok, Enum.sort(Map.to_list(d2))})
    :erlang.display(Ecto.Type.dump(:integer, 5))
    :erlang.display(Ecto.Type.load(:boolean, true))

    # decimal arithmetic (small coefficients — bignum ceiling documented)
    d = Decimal.add(Decimal.new("1.25"), Decimal.new("2.5"))
    :erlang.display(Decimal.to_string(d))
    :erlang.display(Decimal.compare(Decimal.new("2.0"), Decimal.new(2)))

    # changesets under load (GC churn through the whole pipeline)
    :erlang.display(churn(200, 0))

    :erlang.display(:ecto_gate_done)
  end

  defp dump_kw(tag, kw), do: :erlang.display({tag, kw})

  defp churn(0, acc), do: acc

  defp churn(n, acc) do
    attrs = %{"name" => "user#{n}", "email" => "u#{n}@x.y", "age" => rem(n, 100) + 1}
    cs = User.changeset(%User{}, attrs)
    churn(n - 1, acc + if(cs.valid?, do: 1, else: 0))
  end
end
