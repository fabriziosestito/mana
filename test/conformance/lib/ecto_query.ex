defmodule Conf.EctoQuery.User do
  use Ecto.Schema

  schema "users" do
    field :name, :string
    field :email, :string
    field :age, :integer
    field :active, :boolean, default: true
  end
end

defmodule Conf.EctoQuery do
  @moduledoc """
  Ecto.Query building and inspection, no database: literal-source queries,
  runtime composition, schema sources, joins, dynamic/2 and subquery/2 —
  all rendered through inspect/1 (proven by Conf.Inspect).
  """
  import Ecto.Query

  def go do
    min_age = 18

    # literal source: folded at compile time, runtime = struct allocation
    q1 =
      from u in "users",
        where: u.age > ^min_age and u.active,
        select: {u.name, u.age}

    IO.inspect(q1)

    # runtime composition (Builder.*.apply path via Ecto.Queryable)
    q2 = from q in q1, order_by: q.name, limit: 10
    IO.inspect(q2)

    # piped composition + or_where
    q3 =
      "users"
      |> where([u], u.age >= 21)
      |> or_where([u], u.active == false)
      |> select([u], u.email)

    IO.inspect(q3)

    # schema source
    q4 = from u in Conf.EctoQuery.User, where: u.active, select: u.name
    IO.inspect(q4)

    # joins, group_by/having, distinct, offset
    q5 =
      from u in "users",
        join: p in "posts",
        on: p.user_id == u.id,
        group_by: u.id,
        having: count(p.id) > 3,
        distinct: true,
        offset: 5,
        select: {u.id, count(p.id)}

    IO.inspect(q5)

    # dynamic/2 merged into where
    dyn = dynamic([u], u.age < ^99 and not is_nil(u.name))
    q6 = from u in "users", where: ^dyn, select: u.id
    IO.inspect(q6)

    # subquery
    q7 = from s in subquery(q1), select: s.name
    IO.inspect(q7)

    # fragment
    q8 = from u in "users", where: fragment("lower(?)", u.name) == ^"ada", select: u.id
    IO.inspect(q8)

    # select_merge + update-style exprs on a composed query
    q9 = q4 |> select_merge([u], %{age: u.age}) |> limit(3)
    IO.inspect(q9)

    # prefix, as/named bindings
    q10 =
      from u in "users",
        as: :user,
        prefix: "tenant",
        where: as(:user).age > 1,
        select: u.id

    IO.inspect(q10)

    # runtime schema atom through Ecto.Queryable.Atom (code:is_loaded path)
    q11 = Conf.EctoQuery.User |> where([u], u.age > 5) |> select([u], u.id)
    IO.inspect(q11)

    :ok
  end
end
