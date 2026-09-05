defmodule Conf.WsDeflate do
  @moduledoc """
  The counter LiveView driven over a permessage-deflate websocket. The
  client offers the extension, so Bandit compresses its frames (RSV1) and
  expects compressed frames back. This checks the streaming zlib path on
  the websocket hot path. The printed facts are the same decoded join and
  diff facts as in Conf.Ws, plus the negotiated extension and the RSV1
  markers. Raw compressed bytes never print.
  """

  alias Conf.WsClient, as: C

  def go do
    port = C.boot()
    IO.puts(inspect(port > 0))

    {status, headers, body} = C.get(port, "/counter")
    IO.puts(status)
    tokens = C.extract(headers, body)

    # Upgrade WITH a permessage-deflate offer.
    {sock, ws_status, ws_headers, accept_ok} =
      C.upgrade(port, tokens, ["sec-websocket-extensions: permessage-deflate\r\n"])

    IO.puts("upgrade: #{ws_status} #{inspect(accept_ok)}")
    IO.puts("ext: #{Map.get(ws_headers, "sec-websocket-extensions")}")

    ctx = C.deflate_ctx()
    topic = "lv:" <> tokens.id

    # compressed join
    join_payload = %{
      "url" => "http://localhost:#{port}/counter",
      "params" => %{"_csrf_token" => tokens.csrf, "_mounts" => 0},
      "session" => tokens.session,
      "static" => tokens.static
    }

    C.push_deflate(sock, ctx, "1", "1", topic, "phx_join", join_payload)
    {[_, _, ^topic, "phx_reply", reply], rsv_join, _} = C.recv_msg_deflate(sock, ctx)
    IO.puts("join: #{reply["status"]} rsv1=#{rsv_join} #{inspect(reply["response"]["rendered"])}")

    # compressed click event
    C.push_deflate(sock, ctx, "1", "2", topic, "event", %{
      "type" => "click",
      "event" => "inc",
      "value" => %{}
    })

    {[_, _, ^topic, "phx_reply", ev], rsv_ev, _} = C.recv_msg_deflate(sock, ctx)
    IO.puts("click: #{ev["status"]} rsv1=#{rsv_ev} #{inspect(ev["response"])}")

    C.send_close(sock)
    {8, _rsv, _payload, _} = C.recv_frame(sock)
    IO.puts(inspect(:closed))

    IO.puts(inspect(:done))
    :ok
  end
end
