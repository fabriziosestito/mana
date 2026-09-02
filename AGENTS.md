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
- Dependency policy: prefer the Rust stdlib for anything it covers
  adequately — but do NOT hand-roll complex, correctness-critical
  algorithms that a well-established crate provides (bignum arithmetic,
  crypto primitives, regexes). Adding such a crate requires two gates:
  (a) behavior byte-identical to BEAM through the conformance suite, and
  (b) a measured benchmark showing it is at least as fast as the code it
  replaces on OUR workload shapes. Current externals: inkwell, mio,
  corosensei, rayon, blake3, regex, sha1/sha2/hmac, getrandom, dirs.
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
  modes beyond raw are TODO(packet). File/socket/zlib handles are
  `{mana_file, N}` / `{mana_socket, N}` / `{mana_zlib, N}` tuples, not ports
  or NIF refs — `is_port/1` is false on them (documented divergence; only
  user code ever sees them).

- **zlib is real DEFLATE (miniz_oxide), not byte-identical to erlang's
  zlib.** gzip/gunzip/compress/uncompress/zip/unzip plus the streaming API
  (open/inflateInit/deflateInit/deflate/safeInflate/resets/ends) back
  Bandit's permessage-deflate and HTTP gzip. Compressed OUTPUT differs from
  BEAM byte-for-byte (miniz ≠ zlib), so conformance checks inflation of
  fixed blobs + roundtrips, never compressed bytes. deflateInit honors
  level + strategy + the windowBits sign (raw vs zlib); the window
  magnitude, method and memLevel are ignored (miniz always uses a 32K
  window — a decoding superset). Only breaks a peer that requests
  server_max_window_bits < 15, which browsers never do.

- **ets distinguishes set / bag / duplicate_bag** (kind parsed from the
  new/2 options). Bags allow several rows per key; lookup_element returns a
  LIST for bag-kind tables (Registry.dispatch's contract) and a single
  element for set tables. This is what Phoenix.PubSub's Registry needs
  (pid_ets is always a duplicate_bag). Ordered-set iteration, update_counter
  and first/next remain TODO(ets).

- **The build cache must key EVERY codegen input.** manac keeps a
  content-addressed object cache (Go's build-cache model) under the OS user
  cache dir (`~/.cache/mana`, `~/Library/Caches/mana`, `%LOCALAPPDATA%\mana`;
  `MANA_CACHE_DIR` overrides, `MANA_NO_CACHE=1` disables, `MANA_DEBUG_CACHE=1`
  prints hits/misses, `MANA_DEBUG_KEY=<module>` dumps one module's key
  inputs). A module's key hashes: the manac binary itself (rebuilding the
  compiler invalidates everything), target+config, the module's .core source
  text (the AST is a pure function of it given the tool hash), its
  include set, the (gc, raise) verdict of every remote callee, referenced
  missing modules, and the entry flag. If you add ANY new input that
  influences emitted code (a flag, an environment toggle, a new analysis),
  it MUST go into `action_key` — an omission means stale objects that
  "cannot happen" (Go's cgo caching bug is the canonical example). Entries
  trim by age (30 days unused, checked at most daily); publishes are atomic
  renames, safe for concurrent compiles. The mix task keeps a parallel
  cross-project CORE cache (`<user cache>/mana/cores/<elixir>-otp<otp>/`,
  via `:filename.basedir`) — dumped stdlib Core Erlang keyed by beam mtime.
- **Release-style boot: `mix mana.compile --app`.** No hand-written entry
  modules — `Mana.Boot.generate!` precomputes what a BEAM release's boot
  script + application controller do: bakes the merged compile-time config
  (`.app` env ⊕ config.exs ⊕ `MIX_ENV.exs`) as `put_env` data, compiles
  `config/runtime.exs` INTO the generated `Mana.AppBoot` (a local
  mini-Config DSL with Config's deep-merge semantics; `System.get_env`
  runs at native boot — PORT/PHX_SERVER work like a release), and starts
  the app closure dependency-first via direct `Mod.start(:normal, args)`
  calls (there is no application controller; `ensure_all_started` has no
  cut). Skip-list = runtime cuts/BEAM infra/build tools + dev source
  watchers (phoenix_live_reload, file_system); skipped apps still get
  their env baked (except mix/iex/ex_unit/eex). Build-time release
  semantics: `plug_init_mode` forced to `:compile` and dev-only
  build-tool config (code_reloader/live_reload/watchers) scrubbed BEFORE
  compiling (compile_env consumers bake it in), sequenced as
  `loadpaths --no-validate-compile-env` → scrub → compile, with a
  versioned marker forcing one full recompile per build dir when the
  override set changes. Missing-module calls abort at the CALL SITE (BEAM
  loads such code and fails only on execution — guarded dead branches
  like Phoenix's mix_available? stay live). {M,F,Args} literal tuples
  seed the named function at EVERY arity (apply-time args extension —
  Plug.Debugger's banner {M,F,[]} is called /5). The conformance gate
  runs the SAME generated Mana.AppBoot on both runtimes.
- **Sub-binaries, bignums, dirty-tracked minors (the perf campaign).**
  KIND_SUBBIN=13 views `[len<<8|13 | parent | offset]` are produced by
  bin_slice for slices > 64 bytes (smaller ones copy — no parent pinning);
  bin_parts recomputes the data pointer from the parent TERM on every
  access (parents move). Kind 7 is FORBIDDEN for heap headers (collides
  with TAG_FORWARD 0b111 — this shipped and corrupted heaps). Kinds 5/13
  differ only in bit 3: `(k|8)==13` is the shared bin-kind test; inline
  match reads go through bin_base_addr. KIND_BIGNUM=3 `[limbs<<9|sign<<8|3]`
  allocates via alloc_shared — never a GC point, so +,-,* keep no-frame
  fast paths (overflow via tagged-value intrinsics: sadd/ssub on tagged,
  smul on untagged×(b^1)); bit ops on negative bignums abort
  (TODO(bignum-bitops)); >64-bit binary segments abort
  (TODO(bignum-segments)). Minors are dirty-tracked: a parked process is
  scanned only if it ran or received a message since the last minor
  (push_and_wake/send/swap-out set the flag) — this took phx keepalive
  from 630µs to 425µs; eternal objects get their one minor scan from the
  FRESH_ETERNALS list (write-once ⇒ afterwards old/static forever).
  Gates for these paths: Conf.Subbin, Conf.Big, GC-stress
  (MANA_NURSERY_WORDS=512/4096), SMP matrix, Smoke.Phx soak.
- **Compile speed architecture (the compile-speed milestone).** Three
  layers keep warm builds at hash+link:
  1. **Analysis summaries** (`<cache>/summary/`, keyed by tool_hash +
     source blake3): per-fun edges/atoms/dyn-seeding inputs + condensed
     (base, deps) effect facts. On a summary hit the .core is NOT parsed;
     the AST is re-materialized (re-read, hash-VERIFIED, re-parsed) only on
     an object-cache miss. Summaries are produced by the same collectors
     the analysis consumes — never hand-sync the two. `MANA_CHECK_ANALYSIS=1`
     re-runs the reference AST walkers and panics on any divergence;
     `MANA_DEBUG_REACH` dumps the sorted reachable set for diffing.
  2. **Effect fixpoints are condensed**: expr_may_gc/raise exist twice — the
     reference boolean walkers and the cond_* condensers (arm-for-arm
     mirrors; the erlang BIF effect lists are shared fns `erlang_may_gc`/
     `erlang_may_raise`). Change them TOGETHER, then run the suite under
     MANA_CHECK_ANALYSIS=1.
  3. **The mix driver runs one round warm**: `out/manifest` memoizes the
     last successful build's core list (toolchain-keyed); chase pulls
     expand through the beam ImpT import closure (`Mana.Closure`, cut list
     from `manac --print-bif-modules`) so one round absorbs a whole static
     subgraph; the shared core-cache glob is never passed to manac.
  `manac: time: parse=… reach=… gc=… raise=… key=… codegen=… link=…` prints
  on every run — watch it before optimizing anything.
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
  zero-copy). **There is no remembered set**: anything the runtime stores
  into old space or cross-process state (`shared_tuple` fields, spawn
  pending tuples, `pending_kill` exit reasons) must be `promote_term`-ed
  first — an old→young pointer is invisible to minors and dangles after
  one. And the major walk must cover *live shared* state (pdict,
  pending_kill) of RUNNING processes too — only their saved_* fields are
  stale (`walk_proc_shared_roots`). Both were shipped bugs; the soak that
  catches this class is `Smoke.Phx` (10k keep-alive requests) plus the
  `MANA_NURSERY_WORDS=4096` stress pin. Minors are scheduler-local; majors
  stop the world (schedulers
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
