defmodule Conf.Ws do
  @moduledoc """
  Phoenix LiveView over a real websocket, driven by the raw :gen_tcp
  client in Conf.WsClient. Two clients join the counter LiveView. A clicks
  and gets the diff in its reply. B gets the same diff pushed through a
  PubSub broadcast. Only deterministic facts print: statuses, decoded
  rendered and diff structures, and booleans. Tokens, ids, topics, and
  cookies never print.
  """

  alias Conf.WsClient, as: C

  def go do
    port = C.boot()
    IO.puts(inspect(port > 0))

    # Dead render: the page carries the LiveView bootstrap payload.
    {status, headers, body} = C.get(port, "/counter")
    IO.puts(status)
    IO.puts(inspect(String.contains?(body, "Count:")))
    IO.puts(inspect(String.contains?(body, "data-phx-main")))

    tokens = C.extract(headers, body)
    IO.puts(inspect(tokens.session != "" and tokens.csrf != ""))

    # Client B connects and joins first. It will receive the broadcast.
    {b_tokens, b_sock} = connect_and_check(port)
    {_b_topic, b_reply, b_rest} = C.join(b_sock, port, "/counter", b_tokens, "1")
    IO.puts("b join: #{b_reply["status"]} #{inspect(b_reply["response"]["rendered"])}")

    # Client A connects, joins, and clicks.
    {a_tokens, a_sock} = connect_and_check(port)
    {a_topic, a_reply, _a_rest} = C.join(a_sock, port, "/counter", a_tokens, "1")
    IO.puts("a join: #{a_reply["status"]} #{inspect(a_reply["response"]["rendered"])}")

    C.push(a_sock, "1", "2", a_topic, "event", %{
      "type" => "click",
      "event" => "inc",
      "value" => %{}
    })

    {["1", "2", ^a_topic, "phx_reply", ev_reply], _} = C.recv_msg(a_sock)
    IO.puts("a click: #{ev_reply["status"]} #{inspect(ev_reply["response"])}")

    # B receives the broadcast-driven diff push.
    {[_join_ref, nil, _topic, "diff", b_diff], _} = C.recv_msg(b_sock, b_rest)
    IO.puts("b push: #{inspect(b_diff)}")

    # Clean close: the server echoes the close frame.
    C.send_close(a_sock)
    {8, _rsv, _payload, _} = C.recv_frame(a_sock)
    IO.puts(inspect(:closed))

    C.send_close(b_sock)
    {8, _rsv2, _payload2, _} = C.recv_frame(b_sock)
    IO.puts(inspect(:closed))

    IO.puts(inspect(:done))
    :ok
  end

  defp connect_and_check(port) do
    {status, headers, body} = C.get(port, "/counter")
    "HTTP/1.1 200 OK" = status
    tokens = C.extract(headers, body)
    {sock, ws_status, _ws_headers, accept_ok} = C.upgrade(port, tokens)
    IO.puts("upgrade: #{ws_status} #{inspect(accept_ok)}")
    {tokens, sock}
  end
end
