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
  The changeset pipeline — the milestone scoreboard entry: warm BEAM runs
  this at ~1.7µs/iter. The target is beating it.
  """
  alias Bench.Ecto.User

  @attrs %{"name" => "Ada", "email" => "ada@example.com", "age" => 36}
  @bad %{"name" => "A", "age" => 200}

  def run do
    Benchee.run(
      %{
        "changeset valid" => fn -> User.changeset(%User{}, @attrs) end,
        "changeset invalid" => fn -> User.changeset(%User{}, @bad) end
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end
end
