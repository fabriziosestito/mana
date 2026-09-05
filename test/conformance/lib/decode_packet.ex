defmodule Conf.DecodePacket do
  @moduledoc """
  Pins the :erlang.decode_packet(:http_bin | :httph_bin) shapes against
  BEAM before Bandit runs on them. The program checks request and response
  lines, URI forms, known and unknown headers, folding, errors, and `more`
  continuations.
  """

  def go do
    d = fn type, bin -> IO.puts(inspect(:erlang.decode_packet(type, bin, []))) end

    # request lines
    d.(:http_bin, "GET / HTTP/1.1\r\nHost: x\r\n\r\n")
    d.(:http_bin, "POST /a/b?c=1 HTTP/1.0\r\n")
    d.(:http_bin, "DELETE /x HTTP/1.1\r\n")
    d.(:http_bin, "BREW /pot HTTP/1.1\r\n")
    d.(:http_bin, "OPTIONS * HTTP/1.1\r\n")
    d.(:http_bin, "GET http://example.com/p HTTP/1.1\r\n")
    d.(:http_bin, "GET http://example.com:8080/p HTTP/1.1\r\n")
    d.(:http_bin, "GET https://example.com HTTP/1.1\r\n")

    # response line
    d.(:http_bin, "HTTP/1.1 200 OK\r\nrest")
    d.(:http_bin, "HTTP/1.0 404 Not Found\r\n")

    # incomplete input and errors
    d.(:http_bin, "GET / HTT")
    d.(:http_bin, "garbage line\r\nnext")
    d.(:http_bin, "\r\n")

    # headers
    d.(:httph_bin, "Content-Length: 42\r\nrest")
    d.(:httph_bin, "content-length: 42\r\n")
    d.(:httph_bin, "HOST: example\r\n")
    d.(:httph_bin, "X-Custom-Thing: v\r\n")
    d.(:httph_bin, "x-custom-thing: v\r\n")
    d.(:httph_bin, "Accept-Encoding: gzip, deflate\r\n")
    d.(:httph_bin, "Cookie: a=1; b=2\r\n")
    d.(:httph_bin, "Value-Spaces:    padded value  \r\nX")
    d.(:httph_bin, "\r\nbody-bytes")
    d.(:httph_bin, "NoColonHere\r\n")
    d.(:httph_bin, "NoColonHere\r\nX")
    d.(:httph_bin, "\r\n")
    d.(:httph_bin, "Folded: a\r\n  b\r\nX")
    d.(:httph_bin, "Partial-Head")
    d.(:httph_bin, "Connection: keep-alive\r\nConnection: close\r\n\r\n")

    :ok
  end
end
