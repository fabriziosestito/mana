# fib — Elixir compiled to a native binary

Build (needs `manac` from this repo, plus Erlang/OTP, LLVM 22, and a C
compiler):

```sh
cargo build --manifest-path ../../../Cargo.toml   # produces target/debug/manac
MANA_BIN=../../../target/debug/manac mix mana.compile --entry Fib.main/0
./_mana/app                                       # prints 832040
```

`mix mana.compile` compiles the project, extracts Core Erlang from the
entry module's `.beam`, and hands it to `manac`. The `.core` file is kept
in `_mana/` for inspection.
