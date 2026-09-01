defmodule Smoke.Phx do
  @moduledoc "Minimal keepalive hammer for the landing page (segv repro)."
  @secret String.duplicate("mana-secret!", 6)
  @req "GET / HTTP/1.1\r\nhost: bench\r\n\r\n"

  def run do
    :logger.remove_handler(:default)
    Application.put_env(:plug, :validate_header_keys_during_test, false)

    Application.put_env(:phx_app, PhxAppWeb.Endpoint,
      adapter: Bandit.PhoenixAdapter,
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

    {:ok, c} = :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, {:active, false}])
    n =
      case System.get_env("SMOKE_N") do
        nil -> 10_000
        v -> String.to_integer(v)
      end

    loop(c, n)
    IO.puts("survived")
  end

  defp loop(_c, 0), do: :ok


  defp loop(c, n) do
    if rem(n, 100) == 0, do: IO.write(:stderr, "#{n} ")
    :ok = :gen_tcp.send(c, @req)
    read_response(c, "")
    loop(c, n - 1)
  end

  defp read_response(c, acc) do
    case :binary.split(acc, "\r\n\r\n") do
      [head, body] ->
        [_, len] = Regex.run(~r/content-length: (\d+)/i, head)
        read_body(c, body, String.to_integer(len))

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
