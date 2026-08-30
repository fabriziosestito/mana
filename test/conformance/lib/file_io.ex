defmodule Conf.File do
  @moduledoc """
  Real filesystem I/O through Elixir's File module and :file directly.
  Runs inside a program-created scratch dir; every printed value is
  deterministic (list_dir output sorted; stat printed as size/type only).
  """

  @dir "/tmp/mana_conf_file_scratch"

  def go do
    File.rm_rf!(@dir)
    File.mkdir_p!(@dir)

    # whole-file round trip
    p = Path.join(@dir, "a.txt")
    IO.puts(inspect(File.write(p, "hello mana\n")))
    IO.puts(inspect(File.read(p)))
    IO.puts(inspect(File.read!(p) == "hello mana\n"))

    # append via write_file/3
    IO.puts(inspect(:file.write_file(p, "more\n", [:append])))
    IO.puts(inspect(File.read!(p)))

    # missing file errors
    IO.puts(inspect(File.read(Path.join(@dir, "nope"))))
    IO.puts(inspect(:file.delete(Path.join(@dir, "nope"))))

    # exists?/dir?/stat
    IO.puts(inspect(File.exists?(p)))
    IO.puts(inspect(File.dir?(@dir)))
    IO.puts(inspect(File.exists?(Path.join(@dir, "nope"))))
    {:ok, st} = File.stat(p)
    IO.puts(inspect({st.size, st.type, st.access}))
    {:ok, raw} = :file.read_file_info(String.to_charlist(p), [{:time, :posix}])
    IO.puts(inspect(elem(raw, 0)))
    IO.puts(inspect(elem(raw, 1)))
    IO.puts(inspect(is_integer(elem(raw, 4))))

    # dirs and listing (sorted — readdir order is fs-dependent)
    File.mkdir!(Path.join(@dir, "sub"))
    File.write!(Path.join(@dir, "b.txt"), "b")
    File.write!(Path.join([@dir, "sub", "c.txt"]), "c")
    IO.puts(inspect(Enum.sort(File.ls!(@dir))))
    IO.puts(inspect(Enum.sort(File.ls!(Path.join(@dir, "sub")))))
    IO.puts(inspect(File.ls(Path.join(@dir, "nope"))))

    # rename / copy
    IO.puts(inspect(File.rename(Path.join(@dir, "b.txt"), Path.join(@dir, "b2.txt"))))
    IO.puts(inspect(File.exists?(Path.join(@dir, "b.txt"))))
    IO.puts(inspect(:file.copy(p, Path.join(@dir, "a2.txt"))))
    IO.puts(inspect(File.read!(Path.join(@dir, "a2.txt")) == File.read!(p)))

    # handle-based :file — open/read/position/write/close
    {:ok, fd} = :file.open(String.to_charlist(p), [:read, :binary])
    IO.puts(inspect(:file.read(fd, 5)))
    IO.puts(inspect(:file.position(fd, 0)))
    IO.puts(inspect(:file.read(fd, 5)))
    IO.puts(inspect(:file.position(fd, {:eof, 0}) |> elem(0)))
    IO.puts(inspect(:file.read(fd, 1)))
    IO.puts(inspect(:file.close(fd)))

    {:ok, fd2} = :file.open(String.to_charlist(Path.join(@dir, "w.bin")), [:write, :binary])
    IO.puts(inspect(:file.write(fd2, ["ab", ?c, <<"d">>])))
    IO.puts(inspect(:file.close(fd2)))
    IO.puts(inspect(File.read!(Path.join(@dir, "w.bin"))))

    # exclusive create
    IO.puts(inspect(elem(:file.open(String.to_charlist(p), [:write, :exclusive]), 0)))

    # cleanup
    IO.puts(inspect(File.rm(Path.join(@dir, "a2.txt"))))
    IO.puts(inspect(File.rmdir(Path.join(@dir, "sub"))))
    File.rm_rf!(@dir)
    IO.puts(inspect(File.exists?(@dir)))

    :ok
  end
end
