# AGENTS.md

Guidance for AI coding agents working in this repository.

## What this is

**manallvm** is an ahead-of-time compiler that turns Core Erlang into native
binaries (like Go: one static executable, no VM). Erlang/Elixir source is
first lowered to Core Erlang by the standard `erlc`/`elixirc` toolchain; we
compile that to machine code via LLVM and link it against our own Rust
runtime. There is no BEAM anywhere in the output.

Design pillars (do not violate them casually):

- **Closed world.** No hot code loading, no dynamic code loading, no
  distribution. Whole-program knowledge at compile time is the intended
  performance advantage over BEAM.
- **Erlang semantics still apply** where implemented: per-process heaps
  (future GC), guaranteed tail calls (in progress), pattern-match fall-through
  to `match_fail`, immutable terms.

## Layout

- `crates/mana-syntax/` — lexer, parser, and AST for the Core Erlang **as
  actually printed by `erlc +to_core`** (annotations `-| [...]`, annotated
  clauses, `%%` comments), not just the spec grammar.
- `crates/mana-codegen/` — LLVM codegen via inkwell (feature `llvm22-1`,
  needs system LLVM 22). Tagged-term constants, pattern-match compilation,
  BIF lowering, object-file emission.
- `crates/mana-rt/` — the runtime, built as a `staticlib` every binary links
  against. **Its crate docs define the term representation and the
  ProcCtx/GC contract**; read them before touching either side.
- `crates/manac/` — CLI driver: takes one or more `.erl`/`.core` files
  (`.erl` goes through `erlc +to_core`), compiles code reachable from
  `--entry [MODULE:]FUN/ARITY` (default `main/0` in the first file's
  module), links with `cc`. Files that fail to parse are skipped with a
  warning and only become errors if the program needs them.
- `hex/mana/` — the Hex package Elixir projects depend on. Its
  `mix mana.compile --entry Mod.fun/0` task compiles the Mix project,
  extracts textual Core Erlang from every project `.beam`'s debug_info
  (`Mana.CoreDump`: `backend.debug_info(:core_v1, ...)` + `:core_pp.format/1`),
  and invokes `manac` with all of them. Locates the compiler via `--bin` /
  `config :mana, :bin` / `MANA_BIN` / PATH.
- `examples/erlang/` — single-file `.erl` programs used as end-to-end tests;
  `examples/elixir/` — Mix-project examples built via `mix mana.compile`.
- `test/conformance/` — the correctness gate (see below).

## Term representation (the one contract that must never drift)

Terms are 64-bit words, low 3 bits are the tag:

| tag   | meaning                                                       |
|-------|---------------------------------------------------------------|
| 0b000 | boxed pointer; header word = kind (low 8 bits: 0 tuple, 1 float) + arity |
| 0b001 | small integer, value = word >> 3 (arithmetic)                 |
| 0b010 | atom: pointer to `{ len: u64, bytes }` static                 |
| 0b011 | nil `[]` (whole word is 3)                                    |
| 0b100 | cons cell: pointer to `[head, tail]`                          |

`mana-rt/src/lib.rs` and the constants at the top of
`mana-codegen/src/lib.rs` encode this **twice**. If you change one, change
the other in the same commit and re-run the end-to-end check below.

## Build, test, verify

```sh
make build                  # cargo build — everything incl. libmana_rt.a
make test                   # cargo test — unit tests (parser, etc.)
make test-conformance       # THE correctness gate (see below)

# Quick end-to-end smoke checks:
./target/debug/manac -o /tmp/demo examples/erlang/demo.erl && /tmp/demo
./target/debug/manac -o /tmp/fib  examples/erlang/fib.erl  && /tmp/fib  # expect 832040
make example-elixir                                                     # expect 832040
```

**Conformance is the gate.** `test/conformance/` holds `Conf.*` Elixir
modules with a `go/0` that prints via `:erlang.display/1`. The harness runs
each program on BEAM (as a separate OS process — the oracle) and as a
mana-compiled binary, and asserts the stdouts are identical. There are no
golden files; BEAM is always the reference. **A language or runtime feature
without a conformance program covering it is not done.** Add programs by
dropping a module in `test/conformance/lib/`.

A change is not done because `cargo build` passes. Codegen bugs surface only
when a compiled program runs; always run the conformance suite and the
examples. When you add a language feature, add a conformance program that
exercises it.

Requirements: Rust stable (pinned by `rust-toolchain.toml`, needs ≥ 1.88),
LLVM 22 (`llvm-config` on PATH), Erlang/OTP (`erlc`) + Elixir (`mix`), a C
compiler (`cc`).

## Conventions

- Errors are `Result<T, String>` with human-readable messages naming the
  construct and (in the parser) the line number. Keep that shape for now; a
  proper diagnostics type is future work, don't introduce one crate-locally.
- When the parser or codegen meets something unsupported, **fail loudly with
  a specific message** ("letrec is not supported yet (list comprehensions)").
  Never silently skip a construct or emit best-guess code — a wrong binary is
  far worse than a compile error.
- Debt is marked with `TODO(topic):` comments (`TODO(gc)`, `TODO(bignum)`,
  `TODO(lco)`). Keep the convention; grep for these before starting related
  work, and remove the comment when you resolve it.
- The parser must accept **real `erlc +to_core` output**. When extending it,
  generate a real `.core` file first (`erlc +to_core foo.erl`) and develop
  against that, not against the Core Erlang spec's idealized syntax.
- Dependencies are deliberately minimal (inkwell is the only external one).
  Do not add crates for things the stdlib does adequately.
- No `unsafe` outside `mana-rt` term decoding and the GEP helpers in codegen
  that already use it.

## Commits

When asked to commit, this is what is meant:

- Conventional Commits (`feat:`, `fix:`, `chore:`, `docs:`, `refactor:`,
  `test:`), optionally scoped by crate: `feat(codegen): ...`,
  `fix(parser): ...`.
- Subject only — one sentence, imperative mood, no body paragraphs.
- Sign off (`git commit -s`).
- Do not add an AI co-author trailer, a "Generated with ..." footer, or any
  other AI attribution — in commits, PR titles/bodies, or anywhere else.
- Split into several commits when the changes are logically distinct
  (e.g. parser support and codegen support for a feature are usually two
  commits only if each stands alone; otherwise one).

## Pull requests

When asked to open a PR:

- Title follows the same Conventional Commits format as commit subjects.
- Body: what changed and why, which examples/tests prove it, and any new
  TODO debt introduced. Keep it short; no AI attribution (see above).
- A PR that touches codegen or the runtime must state that the end-to-end
  examples were run and what they printed.

## Gotchas

- **One object file per module — keep it that way.** Codegen emits a
  separate object per Core module (a deliberate build-time decision so
  incremental caching and parallel codegen stay possible). Atom identity
  across objects relies on atoms being `linkonce_odr` globals whose symbol
  name is derived from the atom text — the linker keeps one per name. Do
  not merge everything into a single LLVM module, change atom linkage, or
  make atom symbol names non-deterministic.
- **No dynamic atoms.** Atoms exist only as compile-time statics;
  `list_to_atom` and friends are unsupported until a runtime atom table
  exists.
- **There IS a GC now — respect the root discipline.** Each process has a
  heap with a Cheney copying collector (`mana-rt`). Any call into compiled
  code that may allocate is a *GC point*; a term held in an SSA register
  across a GC point is a stale pointer after collection. Codegen enforces
  this via may-GC effect analysis + root frames + structural spills (see
  `mana-codegen` crate docs). When adding codegen features: route sibling
  evaluations through `eval_siblings`/`eval_all_rooted`, never cache a term
  value across an allocation. Functions proven non-allocating are frameless
  — don't break the effect analysis's conservatism.
- **ProcCtx word offsets 0/1/2** (`heap_top`, `heap_end`, `roots_head`) are
  a fixed contract between `mana-rt` and `mana-codegen`; tag `0b111` is the
  GC forwarding marker. Change either only in lockstep, and run the GC
  stress conformance program (`Conf.Gc`). `MANA_GC_LOG=1` prints
  collections.
- **Tail calls are hints, not guarantees.** Calls in tail position get the
  LLVM `tail` marker under the C calling convention. Deep non-self recursion
  can still overflow the stack. The planned fix is `tailcc` + `musttail`
  with a uniform signature — don't ship code that relies on unbounded
  mutual recursion until then.
- **Small ints don't overflow-check.** Arithmetic wraps within the tagged
  range (`TODO(bignum)`). Don't use compiled output for correctness claims
  near ±2^60.
- **Comparisons are int-only.** `<`, `=<` etc. compare raw tagged words,
  which is correct for small ints and identity of immediates, wrong across
  types and for boxed terms. Full term ordering is future work.
- `module_info/0,1` and Elixir's `__info__/1` are never compiled in
  practice: codegen only compiles functions reachable from the entry point.
  Don't remove the reachability pruning — those generated functions use
  constructs codegen rejects (binaries, unsupported BIFs).
- `examples/erlang/*.core`, `*.beam`, `_mana/`, `_build/`, `deps/`, and
  compiled example binaries are gitignored build artifacts — never commit
  them.
