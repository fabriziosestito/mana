defmodule Bench.Phx do
  @moduledoc """
  The scaffolded Phoenix app serving its landing page, measured with a raw
  gen_tcp client: connect+GET+close cycles and keep-alive GETs.
  """

  @secret String.duplicate("mana-secret!", 6)
  @req "GET / HTTP/1.1\r\nhost: bench\r\n\r\n"

  def run do
    :logger.remove_handler(:default)
    Application.put_env(:plug, :validate_header_keys_during_test, false)
    Application.put_env(:phoenix, :json_library, Bench.Env.json_library())
    IO.puts("Bench.Phx: #{Bench.Env.tag()}")

    Application.put_env(:phx_app, PhxAppWeb.Endpoint,
      adapter: Bench.Env.http_adapter(),
      http: [ip: {127, 0, 0, 1}, port: 0],
      server: true,
      secret_key_base: @secret,
      render_errors: [
        formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
        layout: false
      ]
    )

    {:ok, _} = Plug.Application.start(:normal, [])
    {:ok, _} = Phoenix.PubSub.Application.start(:normal, [])
    {:ok, _} = PhxApp.Application.start(:normal, [])
    {:ok, {_ip, port}} = PhxAppWeb.Endpoint.server_info(:http)

    Benchee.run(
      %{
        "phx landing (new conn)" => fn ->
          {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
          :ok = :gen_tcp.send(c, @req)
          read_response(c, "")
          :ok = :gen_tcp.close(c)
        end,
        "phx landing (keepalive)" => {
          fn c ->
            :ok = :gen_tcp.send(c, @req)
            read_response(c, "")
            c
          end,
          before_scenario: fn _ ->
            {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
            c
          end
        }
      },
      warmup: 0.5,
      time: 1.5,
      memory_time: 0,
      reduction_time: 0
    )

    :ok
  end

  defp read_response(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, body] ->
        len =
          case Regex.run(~r/content-length: (\d+)/i, head) do
            [_, n] -> String.to_integer(n)
            _ -> 0
          end

        read_body(c, body, len)

      _ ->
        {:ok, chunk} = :gen_tcp.recv(c, 0, 5000)
        read_response(c, acc <> chunk)
    end
  end

  defp read_body(_c, buf, len) when byte_size(buf) >= len, do: :ok

  defp read_body(c, buf, len) do
    {:ok, more} = :gen_tcp.recv(c, len - byte_size(buf), 5000)
    read_body(c, buf <> more, len)
  end
end
