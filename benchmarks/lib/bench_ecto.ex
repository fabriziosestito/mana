defmodule Bench.Ecto.User do
  use Ecto.Schema
  import Ecto.Changeset

  embedded_schema do
    field :name, :string
    field :email, :string
    field :age, :integer
  end

  def changeset(user, attrs) do
    user
    |> cast(attrs, [:name, :email, :age])
    |> validate_required([:name, :email])
    |> validate_number(:age, greater_than: 0, less_than: 150)
  end
end

defmodule Bench.Ecto do
  @moduledoc """
  The changeset pipeline, the milestone scoreboard entry. Warm BEAM runs
  this at about 1.7µs/iter. The target is to beat it. The query build and
  inspect entry records the starting number of the Ecto.Query milestone.
  """
  import Ecto.Query
  alias Bench.Ecto.User

  @attrs %{"name" => "Ada", "email" => "ada@example.com", "age" => 36}
  @bad %{"name" => "A", "age" => 200}

  def run do
    min_age = 18

    Benchee.run(
      %{
        "changeset valid" => fn -> User.changeset(%User{}, @attrs) end,
        "changeset invalid" => fn -> User.changeset(%User{}, @bad) end,
        "query build+inspect" => fn ->
          q =
            from u in "users",
              where: u.age > ^min_age and u.active,
              order_by: u.name,
              limit: 10,
              select: {u.name, u.age}

          inspect(q)
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
