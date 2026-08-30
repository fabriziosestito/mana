# AGENTS.md

Guidance for AI coding agents working in this repository.

## What this is

**manallvm** is an ahead-of-time compiler that turns Core Erlang into native
binaries (like Go: one static executable, no VM). Erlang/Elixir source is
first lowered to Core Erlang by the standard `erlc`/`elixirc` toolchain; we
compile that to machine code via LLVM and link it against our own Rust
runtime. There is no BEAM anywhere in the output.

Prior art worth consulting: `~/wrk/mana` is the author's earlier
Elixir → **Go** transpiler that walked much of this same road (Ecto
changesets, Plug, benchmarking methodology). Its `PROJECT.md` is an
engineering log of what broke and why — nested-closure shadowing in
Ecto's `validate_change`, the `:re.version → "mana"` regex trick, the
warm-BEAM bench discipline all originated there. Mine it for pitfalls
before re-deriving them; do NOT reference it in this repo's code or docs
(production readers don't know about past experiments — AGENTS.md is the
one place it may be mentioned).

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

- **No blocking syscall may run on a scheduler thread.** The STW requester
  waits for every scheduler to reach a safepoint (loop top / alloc slow
  path); a scheduler stuck in a blocking syscall stalls GC for its whole
  duration. Sockets are therefore NONBLOCKING (mio reactor thread + parked
  processes; the reactor never touches process state — it pushes wake
  tokens/messages drained at scheduler safepoints, same discipline as the
  timer thread). File ops and stdout are the documented exception: direct
  syscalls, µs-scale on local disks — TODO(io-pool) is the real fix. Packet
  modes beyond raw are TODO(packet). File/socket handles are
  `{mana_file, N}` / `{mana_socket, N}` tuples, not ports — `is_port/1` is
  false on them (documented divergence; only user code ever sees them).

- **The build cache must key EVERY codegen input.** manac keeps a
  content-addressed object cache (Go's build-cache model) under the OS user
  cache dir (`~/.cache/mana`, `~/Library/Caches/mana`, `%LOCALAPPDATA%\mana`;
  `MANA_CACHE_DIR` overrides, `MANA_NO_CACHE=1` disables, `MANA_DEBUG_CACHE=1`
  prints hits/misses, `MANA_DEBUG_KEY=<module>` dumps one module's key
  inputs). A module's key hashes: the manac binary itself (rebuilding the
  compiler invalidates everything), target+config, the module's AST, its
  include set, the (gc, raise) verdict of every remote callee, referenced
  missing modules, and the entry flag. If you add ANY new input that
  influences emitted code (a flag, an environment toggle, a new analysis),
  it MUST go into `action_key` — an omission means stale objects that
  "cannot happen" (Go's cgo caching bug is the canonical example). Entries
  trim by age (30 days unused, checked at most daily); publishes are atomic
  renames, safe for concurrent compiles. The mix task keeps a parallel
  cross-project CORE cache (`<user cache>/mana/cores/<elixir>-otp<otp>/`,
  via `:filename.basedir`) — dumped stdlib Core Erlang keyed by beam mtime.
- **Never delete half-built LLVM basic blocks.** Erasing a block that
  another block still branches to leaves dangling references (LLVM's erase
  does not fix up uses) and manifests as glibc heap corruption in manac
  itself. When abandoning a half-compiled function (function-granular
  poisoning), terminate every unterminated block with `unreachable` and
  prepend a fresh stub entry block — O2 removes the dead body.
- **The empty map pattern `~{}~` matches any MAP — but only maps.**
  `Pattern::Map` must emit the is-map kind test even with zero pairs.
  Getting this wrong made `Enum.into/2` silently return its input (erlc
  compiles `%{} = m` catch-all-map clauses everywhere).
- **`=>` vs `:=` in map updates is load-bearing.** erlc rewrites
  `maps:put/3` calls into `~{K => V | M}~` assoc updates; `=>` means
  insert-or-replace (`mana_rt_map_put`), `:=` means the key must exist
  (`mana_rt_map_update_exact`, badkey on miss). Never flatten MapAssoc.
- **BIF modules and native overrides.** `is_bif_module` lists modules never
  compiled from beams (erlang, maps, io, unicode, persistent_term, code,
  io_lib, logger, ets, application, file, erts_internal, elixir_erl,
  erl_eval, beam_lib) — reachability skips them; codegen intercepts calls
  (including `fun m:f/a` captures via mini-compiled shims and tail calls).
  Separately, nif_error stub DEFINITIONS inside compiled modules (lists
  reverse/member/keyfind…, all of binary.erl) are overridden with native
  bodies at definition time so local and remote callers agree.
- **The stdlib arrives via the chase loop.** `mix mana.compile` runs manac,
  batch-pulls every "module 'X' … is not among the compiled" it reports
  (located via `:code.which`, dumped to `_mana/core-cache`, mtime-keyed),
  and also pulls "dynamic module candidate" notes — uncompiled `Elixir.*`
  atoms mentioned in reachable code (that is how consolidated-protocol impl
  modules like String.Chars.Integer arrive; build-tool apps are filtered).
  Reachability seeds exports of mentioned Elixir modules for literally
  named dynamic calls; erlang-side behaviour callbacks are not seeded yet
  (TODO(behaviour-seeding)).
- **One object file per module — keep it that way.** Codegen emits a
  separate object per Core module (a deliberate build-time decision so
  incremental caching and parallel codegen stay possible). Atom identity
  across objects relies on atoms being `linkonce_odr` globals whose symbol
  name is derived from the atom text — the linker keeps one per name. Do
  not merge everything into a single LLVM module, change atom linkage, or
  make atom symbol names non-deterministic.
- **Processes: SMP, per-scheduler nurseries, shared old generation.**
  `MANA_SCHEDULERS=N` (default 1). Processes are corosensei coroutines
  **pinned to home schedulers** — only the home thread touches a process's
  coroutine/cursor/saved fields; cross-thread interaction is mailbox push,
  state flip, condvar wake. Same-scheduler sends are zero-copy (local
  minors scan local mailboxes); cross-scheduler payloads are **promoted to
  the shared old space at send** (young parts copied once; old parts always
  zero-copy). Minors are scheduler-local; majors stop the world (schedulers
  park at safepoints: scheduler loop + alloc slow path). **Yield points are
  a subset of GC points**: reduction checks (ctx word 5) only at framed
  entries after params are rooted — never add preemption where a live term
  sits in an SSA register. When touching scheduler/GC code, run the SMP
  stress matrix: `Conf.Smp` at MANA_SCHEDULERS=2/4/8, 10 runs each, output
  must be identical. Known limits: frameless CPU loops don't preempt or
  reach STW safepoints (unbounded pause latency, not unsoundness); fixed
  stacks (root 32MB, spawned 1MB — TODO(stacks)); per-message mutex costs
  ~7x on the message micro-bench vs the old single-thread runtime — the
  designed fix is BEAM-style ingress/private mailbox splitting (TODO(mailbox)).
- **Exceptions unwind by sentinel, not EH tables.** A raise stores class/
  reason into ctx words 3/4 and returns the reserved word `0b101` (tag 101 —
  never a valid term); calls to may-raise functions (a whole-program
  fixpoint, like may-GC) check it and branch to the enclosing `try` handler
  or propagate. Tail calls propagate for free via the return value. Reason
  terms are built with `mana_rt_alloc_eternal` (never moved; the GC scans
  their fields via a registry). Stacktraces don't exist yet — the catch
  "stacktrace" variable carries the class atom so re-raises keep their
  class (TODO(stacktraces)).
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
  a fixed contract between `mana-rt` and `mana-codegen`: compiled code bumps
  the nursery inline through words 0/1 and calls `mana_rt_alloc_slow` on
  overflow. Tag `0b111` is the GC forwarding marker; a frame slot containing
  0 is empty (frames are memset-zeroed). The collector is generational
  (adaptive nursery + chunked old space) and relies on term immutability —
  old objects never point young, so there are no write barriers; **never
  emit code that mutates an existing heap term's fields** after
  construction. Change any of this only in lockstep across both crates, and
  run the GC stress program (`Conf.Gc`). `MANA_GC_LOG=1` prints collections.
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
