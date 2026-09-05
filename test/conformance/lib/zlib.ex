defmodule Conf.Zlib do
  @moduledoc """
  zlib streaming and one-shots against BEAM. Compressed *output* can never
  byte-match BEAM, because miniz_oxide is not zlib. This program prints
  only deterministic facts: fixed blobs (generated once from real zlib)
  inflated back to their plaintext, and roundtrip and structural booleans.
  Compressed bytes or sizes never print.
  """

  # Fixed reference blobs produced by the Erlang :zlib. Inflation is
  # deterministic, so the decode of these blobs is the byte-identical gate.
  @gz Base.decode16!(
        "1f8b08000000000000030bc94855282ccd4cce56482aca2fcf5348cbaf50c82acd2d2856c82f4b2d5228014ae72456552aa4e4a7eb7101006acc50eb2d000000",
        case: :lower
      )
  @zc Base.decode16!("789c4b4c4a4e24170100bcbe16f9", case: :lower)
  @raw Base.decode16!(
         "2b482dca4d2d2e4e4c4fd54d494dcb492c49552848acccc94f4c0100",
         case: :lower
       )

  def go do
    # 1. Fixed-blob inflation (the deterministic byte gate).
    IO.puts(:zlib.gunzip(@gz))
    IO.puts(:zlib.uncompress(@zc))
    IO.puts(raw_inflate(@raw))

    # 2. Roundtrips (booleans).
    msg = "The quick brown fox jumps over the lazy dog.\n"
    big = String.duplicate("mana loves phoenix liveview! ", 50)
    IO.puts(inspect(:zlib.gunzip(:zlib.gzip(msg)) == msg))
    IO.puts(inspect(:zlib.uncompress(:zlib.compress(big)) == big))
    IO.puts(inspect(:zlib.unzip(:zlib.zip(big)) == big))
    IO.puts(inspect(stream_roundtrip(big) == big))

    # 3. Structural facts (booleans).
    IO.puts(inspect(byte_size(:zlib.gzip(big)) < byte_size(big)))
    IO.puts(inspect(sync_tail() == <<0, 0, 255, 255>>))
    IO.puts(inspect(reset_reuse() == {msg, msg}))

    IO.puts(inspect(:done))
    :ok
  end

  # Raw (headerless) inflate of a finished deflate stream through safeInflate.
  defp raw_inflate(data) do
    z = :zlib.open()
    :zlib.inflateInit(z, -15)
    out = drain(z, data)
    :zlib.close(z)
    IO.iodata_to_binary(out)
  end

  defp drain(z, data) do
    case :zlib.safeInflate(z, data) do
      {:continue, out} -> [out | drain(z, [])]
      {:finished, out} -> [out]
    end
  end

  # Deflate (raw, sync flush), then inflate back. The roundtrip is symmetric
  # on either runtime even though the compressed bytes differ from BEAM.
  defp stream_roundtrip(data) do
    zd = :zlib.open()
    :zlib.deflateInit(zd, :default, :deflated, -15, 8, :default)
    comp = IO.iodata_to_binary(:zlib.deflate(zd, data, :sync))
    :zlib.close(zd)

    zi = :zlib.open()
    :zlib.inflateInit(zi, -15)
    out = IO.iodata_to_binary(drain(zi, comp))
    :zlib.close(zi)
    out
  end

  # A sync-flushed empty deflate ends with the 00 00 FF FF marker.
  defp sync_tail() do
    z = :zlib.open()
    :zlib.deflateInit(z, :default, :deflated, -15, 8, :default)
    out = IO.iodata_to_binary(:zlib.deflate(z, "x", :sync))
    :zlib.close(z)
    binary_part(out, byte_size(out) - 4, 4)
  end

  # deflateReset lets one stream compress two independent messages.
  defp reset_reuse() do
    m = "The quick brown fox jumps over the lazy dog.\n"
    z = :zlib.open()
    :zlib.deflateInit(z, :default, :deflated, -15, 8, :default)
    a = IO.iodata_to_binary(:zlib.deflate(z, m, :finish))
    :zlib.deflateReset(z)
    b = IO.iodata_to_binary(:zlib.deflate(z, m, :finish))
    :zlib.close(z)
    {raw_inflate(a), raw_inflate(b)}
  end
end
