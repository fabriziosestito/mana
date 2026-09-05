# AGENTS.md

Guidance for AI coding agents that work in this repository.

## What this is

**manallvm** is an ahead-of-time compiler. It turns Core Erlang into one static
native binary. There is no virtual machine in the output. The standard
`erlc` and `elixirc` tools lower Erlang and Elixir to Core Erlang. manallvm
compiles that Core Erlang to machine code with LLVM. The binary links against
our own runtime, written in Rust.

Prior art: `~/wrk/mana` is the author's earlier Elixir to **Go** transpiler.
Its `PROJECT.md` is an engineering log of what broke and why. Read it for
pitfalls before you derive them again. Do NOT reference it in this
repository's code or docs. This file is the one place where it can be named.

Design pillars. Do not break them without a decision from the author.

- **Closed world.** No hot code loading, no dynamic code loading, no
  distribution. Whole-program knowledge at compile time is the intended
  performance advantage over BEAM.
- **Erlang semantics apply** where they are implemented: per-process heaps
  with a generational GC, guaranteed tail calls, pattern-match fall-through
  to `match_fail`, immutable terms.

## Layout

- `crates/mana-syntax/` — lexer, parser, and AST for Core Erlang **as
  `erlc +to_core` prints it** (annotations `-| [...]`, annotated clauses,
  `%%` comments), not only the specification grammar.
- `crates/mana-codegen/` — LLVM codegen with inkwell (feature `llvm22-1`,
  needs system LLVM 22). Modules:
  - `lib.rs` — the `Cg` struct, the term constants that mirror the runtime,
    shared small types.
  - `driver.rs` — `compile_program`, the object cache, the action key.
  - `effects.rs` — the may-GC and may-raise analysis and its condensers.
  - `reach.rs` — reachability, BIF module list, native manifest.
  - `summary.rs` — analysis summaries (`<cache>/summary/`).
  - `cg/abi.rs` — the uniform `tailcc` ABI, runtime extern declarations,
    memory helpers.
  - `cg/statics.rs` — atom globals, constant terms, atom and export tables,
    object emission.
  - `cg/frame.rs` — root frames and slots. `cg/exc.rs` — raise, unwind,
    `check_exc`.
  - `cg/module.rs` — module compilation, lifts, `main`. `cg/expr.rs` —
    expressions. `cg/closure.rs` — apply, closures, letrec.
  - `cg/arith.rs` — arithmetic fast paths, kind tests, binary addressing.
  - `cg/case.rs` — let, literals, case dispatch. `cg/pattern.rs` — pattern
    and binary matching. `cg/binary.rs` — binary construction.
  - `cg/bif.rs` — `compile_bif` dispatch. `cg/bif_erlang.rs` — the `erlang`
    BIFs by family. `cg/bif_native.rs` — the other BIF modules.
    `cg/maps.rs` — maps.
- `crates/mana-rt/` — the runtime, a `staticlib` that every binary links.
  **Its crate docs and `term.rs` define the term representation and the
  ProcCtx/GC contract.** Read them before you touch either side. Modules:
  - `term.rs` — tags, kinds, atoms, allocation primitives, error helpers.
  - `sched.rs` — `ProcCtx`, processes, schedulers. `gc.rs` — minor and
    major collection, promotion.
  - `signals.rs` — links, monitors, exit signals. `proc.rs` — spawn,
    send, receive primops, process dictionary, name registry.
  - `arith.rs` — numbers (`bigint.rs` holds the limb math). `compare.rs`
    — term order, equality, list and tuple BIFs. `maps.rs`, `binary.rs`,
    `convert.rs`, `io.rs`, `etf.rs`, `re.rs`, `codec.rs` (crypto, zlib).
  - `reactor.rs` — the mio thread. `tcp.rs`, `file.rs`, `decode_packet.rs`.
  - `system.rs` — time, timers, system info. `ets.rs` — ets,
    persistent_term, application env. `apply.rs` — export table, apply,
    code BIFs. `native.rs` — the ABI for `Mana.Native` packages.
- `crates/manac/` — CLI driver. It takes `.erl` or `.core` files (`.erl`
  goes through `erlc +to_core`), compiles code reachable from
  `--entry [MODULE:]FUN/ARITY`, and links with `cc`. The default entry is
  `main/0` in the first file. A file that fails to parse gives a warning.
  It becomes an error only if the program needs it.
- `hex/mana/` — the Hex package that Elixir projects depend on. Its
  `mix mana.compile --entry Mod.fun/0` task compiles the Mix project,
  extracts Core Erlang from every project `.beam` (`Mana.CoreDump`), and
  calls `manac` with all of them. It finds the compiler through `--bin`,
  `config :mana, :bin`, `MANA_BIN`, or PATH.
- `hex/mana_json/` — the native JSON package (`Mana.Native` example).
- `examples/erlang/` — single-file `.erl` end-to-end tests.
  `examples/elixir/`, `examples/phoenix/` — Mix projects built with
  `mix mana.compile`.
- `test/conformance/` — the correctness gate (see below).
- `benchmarks/` — benchee suites that run on both runtimes.
- `docs/architecture.md` — the design document.

## Term representation (the contract that must never drift)

Terms are 64-bit words. The low 3 bits are the tag.

| tag   | meaning                                                          |
|-------|------------------------------------------------------------------|
| 0b000 | boxed pointer. The header word holds the kind (low 8 bits) and the size |
| 0b001 | small integer, value = word >> 3                                 |
| 0b010 | atom: pointer to a static `{ len: u64, bytes }`                  |
| 0b011 | nil `[]` (the whole word is 3)                                   |
| 0b100 | cons cell: pointer to `[head, tail]`                             |
| 0b101 | the exception sentinel (never a valid term)                      |
| 0b110 | pid or reference, immediate. Bit 3 selects: `0110` pid, `1110` ref |
| 0b111 | GC forwarding marker (never a valid heap header kind)            |

Box kinds: 0 tuple, 1 float, 2 fun, 3 bignum, 4 map, 5 binary, 13 sub-binary.
Kind 7 is forbidden. `ProcCtx` words 0 to 6 are fixed: `heap_top`,
`heap_end`, `roots_head`, `exc_class`, `exc_reason`, `reductions`,
`argv_spill`.

`crates/mana-rt/src/term.rs` and the constants at the top of
`crates/mana-codegen/src/lib.rs` encode this **twice**. If you change one,
change the other in the same commit. Then run the end-to-end checks below.

## Build, test, verify

```sh
make build                  # cargo build — everything, including libmana_rt.a
make test                   # cargo test — unit tests (parser and more)
make test-conformance       # THE correctness gate (see below)

# Quick end-to-end smoke checks:
./target/debug/manac -o /tmp/demo examples/erlang/demo.erl && /tmp/demo
./target/debug/manac -o /tmp/fib  examples/erlang/fib.erl  && /tmp/fib  # expect 832040
make example-elixir                                                     # expect 832040
```

**Conformance is the gate.** `test/conformance/` holds `Conf.*` Elixir
modules with a `go/0` function that prints with `:erlang.display/1`. The
harness runs each program on BEAM (a separate OS process, the oracle) and as
a mana-compiled binary. The two stdouts must be identical. There are no
golden files. BEAM is always the reference. **A language or runtime feature
without a conformance program is not done.** To add a program, put a module
in `test/conformance/lib/`.

A change is not done because `cargo build` passes. Codegen bugs appear only
when a compiled program runs. Always run the conformance suite and the
examples. When you add a language feature, add a conformance program for it.

Stress matrix for scheduler, GC, or mailbox changes: run the suite with
`MANA_NURSERY_WORDS=512` and `4096`, each with `MANA_SCHEDULERS=2` and `8`.
Run `MANA_CHECK_ANALYSIS=1` when you touch the effect analysis.

Requirements: Rust stable (`rust-toolchain.toml`), LLVM 22 (`llvm-config` on
PATH), Erlang/OTP (`erlc`) and Elixir (`mix`), a C compiler (`cc`).

## Conventions

- **Never reference the prior Go implementation in code.** `~/wrk/mana` is
  prior art to read for pitfalls. It must NOT appear in this repository's
  code, comments, docstrings, or shipped docs. Do not write "mirrors the Go
  reference", "like the Go version", or "the Go BIF". Describe behavior on
  its own terms. Do not name Go the language in code comments either.
- Errors are `Result<T, String>` with a message that names the construct
  and, in the parser, the line number. Keep that shape. A diagnostics type is
  future work. Do not introduce one in a single crate.
- If the parser or codegen meets an unsupported construct, **fail with a
  specific message** ("letrec is not supported yet (list comprehensions)").
  Never skip a construct or emit best-guess code. A wrong binary is far
  worse than a compile error.
- Debt is marked with `TODO(topic):` comments (`TODO(gc)`, `TODO(bignum)`,
  `TODO(stacktraces)`). Grep for these before you start related work. Remove
  the comment when you resolve it.
- The parser must accept **real `erlc +to_core` output**. To extend it,
  generate a real `.core` file first (`erlc +to_core foo.erl`). Develop
  against that file, not against the idealized grammar of the specification.
- Dependency policy: prefer the Rust standard library for what it covers.
  Do NOT hand-roll complex, correctness-critical algorithms that a
  well-established crate provides (crypto primitives, regexes, DEFLATE). A
  new crate must pass two gates. (a) Its behavior is identical to BEAM
  through the conformance suite. (b) A benchmark shows that it is at least as
  fast as the code it replaces, on OUR workload shapes. Bignum limb math is
  hand-rolled because the A/B benchmark showed num-bigint 2 to 9 times
  slower on our 1 to 2 limb shapes. Current externals: inkwell, mio,
  corosensei, crossbeam-queue, parking_lot, rayon, blake3, regex, rustc-hash,
  sha1/sha2/hmac, getrandom, miniz_oxide, unicode-normalization, dirs.
- No `unsafe` outside `mana-rt` term decoding and the GEP helpers in codegen
  that already use it.
- **What can be native (the BIF rule).** `mana-rt` implements BIFs only. The
  test is: "on BEAM, is this function C (BIF/NIF) or is it Erlang/Elixir
  code?"
  1. BIF/NIF on BEAM (`erlang:*`, `binary:*`, `maps:*`, `unicode`, `re`,
     `zlib`, `crypto`, `ets`, `os` nif stubs, ...) → native in `mana-rt` is
     correct. This is parity, not a shortcut.
  2. Erlang/Elixir code on BEAM (`Base`, `String`, `Enum`, `Keyword`, ...) →
     stays compiled code here. If our compiled version is slow, that is a
     **codegen shape problem**. Fix the class (how such code is lowered), not
     the instance. Never port a library function into the runtime for speed.
     That path ends in a second standard library with different semantics.
  3. Compiler-gap exception: a native replacement is allowed when the source
     uses a construct that manac cannot compile yet (sub-byte bitstrings →
     `Elixir.Float.round/ceil/floor`, ports → `Elixir.System.cmd`). Each one
     carries a `TODO(...)` that names the gap. Delete it when the gap closes.
     Do not add new ones for code that compiles today.
  4. Opt-in native library code ships in a hex package through `Mana.Native`
     (`hex/mana_json`). It is never swapped under the standard library.
- `TODO(native-bridge)`: a `Mana.Native` package runs on the scheduler thread
  of the calling process. It can call only process-context `mana_rt_*` entry
  points. A package that wants its own Rust runtime (a tokio reactor, a
  thread pool, a native server that owns sockets) needs a runtime bridge.
  That bridge does not exist yet. It needs three operations:
  1. Message injection into a pid from a foreign thread.
  2. Spawn from outside a scheduler.
  3. Park and wake on an arbitrary fd or event.
  Design it as a small set of `mana_rt_native_*` exports over the reactor and
  timer patterns (`SegQueue` plus a scheduler wake at the loop-top safepoint,
  eternal or shared-space terms only).

## Writing

This repository uses the `simple-english` skill (ASD-STE100 Simplified
Technical English, pragmatic mode) for ALL text. This covers documentation,
code comments, commit messages, and the messages that the compiler and the
mix task print. `.claude/settings.json` sets the output style for Claude
Code.
If the skill is available, invoke it before you write. If it is not, obey
the rules below.

Classify first. Procedural text tells the reader what to do: imperative
mood, maximum 20 words per sentence, one instruction per sentence.
Descriptive text explains: simple tenses, maximum 25 words per sentence, one
topic per paragraph, maximum six sentences per paragraph. Do not mix the two
in one passage.

Rules:

- Verbs: infinitive, imperative, simple present, simple past, simple future,
  past participle as adjective. No present perfect. No "-ing" verb forms.
  Active voice.
- Modals: only `can`, `will`, `must`. Never `should`, `would`, `may`,
  `might`, `could`. For "should": write `must` if required, delete if
  optional.
- Sentences: no contractions, keep articles, keep "that". No semicolons.
  Put the condition before the command: "If the test fails, read the log."
  Use a vertical list for more than two items or steps.
- Words: one word, one meaning, for the whole document. Use `check` for
  check/verify/confirm. Noun chains of maximum three words. Delete words
  that carry no fact (simply, robust, comprehensive, leverage, "in order
  to", "it is worth noting"). Write "for example", not "e.g.". American
  spelling.
- Warnings: command or condition first, then the risk. "Do not run this
  against production. The command deletes rows."
- Never touch code, identifiers, CLI commands, file paths, quoted error
  messages, or product names. Each counts as one word.
- Code comments state a constraint that the code cannot show. Do not write
  a comment that says what the next line does.

Self-check before you deliver: scan for contractions, "has been", "should",
", making", and semicolons. Count the words in your three longest sentences
and split any that are over the limit.

## Commits

When asked to commit, this is what is meant:

- Conventional Commits (`feat:`, `fix:`, `chore:`, `docs:`, `refactor:`,
  `test:`), with an optional crate scope: `feat(codegen): ...`,
  `fix(parser): ...`.
- Subject only. One sentence, imperative mood, no body paragraphs.
- Sign off (`git commit -s`).
- Do not add an AI co-author trailer, a "Generated with ..." footer, or any
  other AI attribution. This applies to commits, PR titles, PR bodies, and
  everywhere else.
- Split logically distinct changes into separate commits. Parser support and
  codegen support for one feature are two commits only if each stands alone.

## Pull requests

When asked to open a PR:

- The title follows the Conventional Commits format of commit subjects.
- The body states what changed and why, which examples and tests prove it,
  and any new `TODO` debt. Keep it short. No AI attribution (see above).
- A PR that touches codegen or the runtime must state that the end-to-end
  examples ran and what they printed.

## Gotchas

- **No blocking syscall on a scheduler thread.** The stop-the-world
  requester waits for every scheduler to reach a safepoint (loop top or
  alloc slow path). A scheduler in a blocking syscall stalls GC for the
  whole call. Sockets are therefore NONBLOCKING: a mio reactor thread plus
  parked processes. The reactor never touches process state. It pushes wake
  tokens and messages that schedulers drain at safepoints, like the timer
  thread. File operations and stdout are the documented exception: direct
  syscalls, microseconds on local disks. `TODO(io-pool)` is the real fix.
  Packet modes beyond raw are `TODO(packet)`. File, socket, and zlib handles
  are `{mana_file, N}`, `{mana_socket, N}`, `{mana_zlib, N}` tuples, not
  ports or NIF references. `is_port/1` is false on them. Only user code
  sees them.

- **zlib is real DEFLATE (miniz_oxide), not byte-identical to Erlang's
  zlib.** The one-shot calls (gzip, gunzip, compress, uncompress, zip,
  unzip) and the streaming API (open, inflateInit, deflateInit, deflate,
  safeInflate, resets, ends) are implemented. Bandit's permessage-deflate and
  HTTP gzip use them. The compressed OUTPUT
  differs from BEAM byte for byte. Conformance therefore checks inflation of
  fixed blobs and round trips, never compressed bytes. `deflateInit` honors
  the level, the strategy, and the sign of `windowBits` (raw or zlib). The
  window size, the method, and `memLevel` are ignored. miniz always uses a
  32K window, a decoding superset. Only a peer that requests
  `server_max_window_bits < 15` breaks. Browsers never do.

- **ets distinguishes set, bag, and duplicate_bag.** The kind comes from the
  `new/2` options. Bags allow several rows per key. `lookup_element` returns
  a LIST for bag-kind tables (the contract of `Registry.dispatch`) and one
  element for set tables. Phoenix.PubSub's Registry needs this (`pid_ets` is
  always a duplicate_bag). Ordered-set iteration, `update_counter`, and
  `first/next` remain `TODO(ets)`.

- **The build cache must key EVERY codegen input.** manac keeps a
  content-addressed object cache under the OS user cache directory
  (`~/.cache/mana`, `~/Library/Caches/mana`, `%LOCALAPPDATA%\mana`).
  `MANA_CACHE_DIR` overrides the location. `MANA_NO_CACHE=1` disables the
  cache. `MANA_DEBUG_CACHE=1` prints hits and misses. `MANA_DEBUG_KEY=<module>`
  dumps the key inputs of one module. A module key hashes these inputs:
  - the manac binary (a rebuilt compiler invalidates everything)
  - target and config
  - the `.core` source text and the include set
  - the (gc, raise) verdict of every remote callee
  - the referenced missing modules and the entry flag
  If you add ANY
  input that influences emitted code (a flag, an environment toggle, a new
  analysis), it MUST go into `action_key`. An omission means stale objects.
  Entries expire after 30 days unused, checked at most daily. Publishes are
  atomic renames, safe for concurrent compiles. The mix task keeps a
  cross-project CORE cache (`<user cache>/mana/cores/<elixir>-otp<otp>/`)
  of dumped standard-library Core Erlang, keyed by beam mtime.

- **Release-style boot: `mix mana.compile --app`.** There are no
  hand-written entry modules. `Mana.Boot.generate!` precomputes what a BEAM
  release boot script and the application controller do. It bakes the merged
  compile-time config (`.app` env, `config.exs`, `MIX_ENV.exs`) as `put_env`
  data. It compiles `config/runtime.exs` INTO the generated `Mana.AppBoot`
  (a local mini-Config DSL with Config's deep-merge semantics), so
  `System.get_env` runs at native boot and `PORT`/`PHX_SERVER` work like a
  release. It starts the app closure dependency-first with direct
  `Mod.start(:normal, args)` calls. There is no application controller and
  `ensure_all_started` has no cut. The skip list holds runtime cuts, BEAM
  infrastructure, build tools, and dev source watchers (phoenix_live_reload,
  file_system). Skipped apps still get their env baked, except mix, iex,
  ex_unit, and eex. Build-time release semantics: `plug_init_mode` is forced
  to `:compile`, and dev-only build-tool config (code_reloader, live_reload,
  watchers) is scrubbed BEFORE compilation, because compile_env consumers
  bake it in. The sequence is `loadpaths --no-validate-compile-env`, scrub,
  compile. A versioned marker forces one full recompile per build directory
  when the override set changes. A call to a missing module aborts at the
  CALL SITE. BEAM loads such code and fails only on execution, so guarded
  dead branches like Phoenix's `mix_available?` stay live. `{M,F,Args}`
  literal tuples seed the named function at EVERY arity (apply-time argument
  extension: Plug.Debugger's banner `{M,F,[]}` is called with 5 arguments).
  The conformance gate runs the SAME generated `Mana.AppBoot` on both
  runtimes.

- **Sub-binaries, bignums, dirty-tracked minors.** `KIND_SUBBIN=13` views
  `[len<<8|13 | parent | offset]` come from `bin_slice` for slices over 64
  bytes. Smaller slices copy, so they do not pin the parent. `bin_parts`
  recomputes the data pointer from the parent TERM on every access, because
  parents move. Kind 7 is FORBIDDEN for heap headers: it collides with
  `TAG_FORWARD` 0b111, and this shipped once and corrupted heaps. Kinds 5 and
  13 differ only in bit 3, so `(k|8)==13` is the shared binary-kind test.
  Inline match reads go through `bin_base_addr`. `KIND_BIGNUM=3`
  `[limbs<<9|sign<<8|3]` allocates with `alloc_shared`, never a GC point, so
  `+`, `-`, `*` keep frameless fast paths. Overflow detection uses the
  tagged-value intrinsics (`sadd`/`ssub` on tagged words, `smul` on
  untagged). Bit operations on negative bignums abort (`TODO(bignum-bitops)`).
  Binary segments over 64 bits abort (`TODO(bignum-segments)`). Minors are
  dirty-tracked: a parked process is scanned only if it ran or received a
  message since the last minor (`push_and_wake`, `send`, and swap-out set
  the flag). Eternal objects get one minor scan from the `FRESH_ETERNALS`
  list. They are write-once, so afterwards they are old forever. Gates for
  these paths: `Conf.Subbin`, `Conf.Big`, the stress matrix, `Smoke.Phx`.

- **Compile speed architecture.** Three layers keep warm builds at hash plus
  link time:
  1. **Analysis summaries** (`<cache>/summary/`, keyed by tool hash plus
     source blake3): per-function edges, atoms, dynamic-seeding inputs, and
     condensed (base, deps) effect facts. On a summary hit the `.core` is
     NOT parsed. The AST is re-read, hash-checked, and re-parsed only on an
     object-cache miss. The same collectors produce the summaries and feed
     the analysis. Never sync the two by hand. `MANA_CHECK_ANALYSIS=1` runs
     the reference AST walkers too and panics on any divergence.
     `MANA_DEBUG_REACH` dumps the sorted reachable set.
  2. **Effect fixpoints are condensed.** `expr_may_gc` and `expr_may_raise`
     exist twice: the reference boolean walkers and the `cond_*` condensers,
     arm for arm. The `erlang` BIF effect lists are the shared functions
     `erlang_may_gc` and `erlang_may_raise`. Change them TOGETHER. Then run
     the suite with `MANA_CHECK_ANALYSIS=1`.
  3. **The mix driver runs one round warm.** `out/manifest` memoizes the core
     list of the last successful build (toolchain-keyed). The chase loop
     pulls the beam `ImpT` import closure (`Mana.Closure`, cut list from
     `manac --print-bif-modules`), so one round absorbs a whole static
     subgraph. The shared core-cache glob is never passed to manac.
  `manac: time: parse=… reach=… gc=… raise=… key=… codegen=… link=…` prints on
  every run. Read it before you optimize anything.

- **Never delete half-built LLVM basic blocks.** If another block still
  branches to an erased block, LLVM leaves dangling references. The symptom
  is glibc heap corruption inside manac. To abandon a half-compiled function
  (function-granular poisoning), terminate every open block with
  `unreachable` and prepend a fresh stub entry block. O2 removes the dead
  body.

- **The empty map pattern `~{}~` matches any MAP, and only maps.**
  `Pattern::Map` must emit the is-map kind test even with zero pairs. Without
  it, `Enum.into/2` returned its input, because erlc compiles `%{} = m`
  catch-all-map clauses everywhere.

- **`=>` and `:=` in map updates are different.** erlc rewrites `maps:put/3`
  into `~{K => V | M}~` assoc updates. `=>` means insert-or-replace
  (`mana_rt_map_put`). `:=` means the key must exist
  (`mana_rt_map_update_exact`, badkey on a miss). Never flatten `MapAssoc`.

- **BIF modules and native overrides.** `is_bif_module` lists modules that
  are never compiled from beams (erlang, maps, io, unicode, persistent_term,
  code, io_lib, logger, ets, application, file, erts_internal, elixir_erl,
  erl_eval, beam_lib). Reachability skips them. Codegen intercepts calls to
  them, including `fun m:f/a` captures through mini-compiled shims and tail
  calls. Separately, `nif_error` stub DEFINITIONS inside compiled modules
  (lists reverse/member/keyfind, all of binary.erl) get native bodies at
  definition time, so local and remote callers agree.

- **The standard library arrives through the chase loop.** `mix
  mana.compile` runs manac. For every "module 'X' … is not among the
  compiled" report, it locates the module with `:code.which` and dumps it to
  `_mana/core-cache`, keyed by mtime. It also pulls the "dynamic
  module candidate" notes: uncompiled `Elixir.*` atoms in reachable code.
  That is how consolidated-protocol implementation modules like
  `String.Chars.Integer` arrive. Build-tool apps are filtered out.
  Reachability seeds the exports of named Elixir modules for literal dynamic
  calls. Erlang-side behaviour callbacks are not seeded yet
  (`TODO(behaviour-seeding)`).

- **One object file per module. Keep it that way.** Codegen emits one object
  per Core module, so incremental caching and parallel codegen stay
  possible. Atom identity across objects relies on `linkonce_odr` globals
  whose symbol name derives from the atom text. The linker keeps one per
  name. Do not merge everything into one LLVM module, do not change atom
  linkage, and do not make atom symbol names non-deterministic.

- **Processes: SMP, per-scheduler nurseries, shared old generation.**
  `MANA_SCHEDULERS=N` (default 1). Processes are corosensei coroutines
  **pinned to home schedulers**. Only the home thread touches the coroutine,
  cursor, and saved fields of a process. Cross-thread interaction is a
  mailbox push, a state flip, or a condvar wake. Same-scheduler sends are
  zero-copy, because local minors scan local mailboxes. Cross-scheduler
  payloads are **promoted to the shared old space at send**: young parts are
  copied once, old parts stay zero-copy. **There is no remembered set.**
  Anything that the runtime stores into old space or into cross-process
  state (`shared_tuple` fields, spawn pending tuples, `pending_kill` exit
  reasons) must go through `promote_term` first. An old-to-young pointer is
  invisible to minors and dangles after one. The major walk must also cover
  the live shared state (pdict, `pending_kill`) of RUNNING processes. Only
  their `saved_*` fields are stale (`walk_proc_shared_roots`). Both were
  shipped bugs. The soak that catches this class is `Smoke.Phx` (10k
  keep-alive requests) plus `MANA_NURSERY_WORDS=4096`. Minors are
  scheduler-local. Majors stop the world: schedulers park at safepoints (the
  scheduler loop and the alloc slow path). **Yield points are a subset of GC
  points.** Reduction checks (ctx word 5) happen only at framed entries after
  the parameters are rooted. Never add preemption where a live term sits in
  an SSA register. When you touch scheduler or GC code, run `Conf.Smp` at
  `MANA_SCHEDULERS=2/4/8`, 10 runs each. The output must be identical. Known
  limits: frameless CPU loops do not preempt and do not reach STW safepoints
  (unbounded pause latency, not unsoundness). Stacks are fixed: 32 MB root,
  1 MB spawned (`TODO(stacks)`).

- **The mailbox is ingress plus private queue plus cursor.** Senders push
  to the lock-free `ingress`. The owner drains it into `private` (a
  `VecDeque`) at receive time. `cursor` is the BEAM save pointer. A receive
  that times out resets the cursor, so the messages it skipped are visible to
  the next receive. Bandit depends on this: `{:plug_conn, :sent}` sits behind
  a `receive ... after 0` flush on every keep-alive request.
  `message_queue_len` is `private.len() + ingress.len()`. Lost-wakeup
  protocol for every park (`recv_wait`, `park_on_socket`, `hibernate`):
  publish `Waiting` under the state lock, then re-check the ingress.

- **Exceptions unwind by sentinel, not EH tables.** A raise stores the class
  and reason into ctx words 3 and 4. Then it returns the reserved word
  `0b101`. Calls to may-raise functions (a whole-program fixpoint, like
  may-GC) check the result. They branch to the enclosing `try` handler, or
  they propagate. Tail
  calls propagate for free through the return value. Reason terms are built
  with `mana_rt_alloc_eternal`. They never move. The GC scans their fields
  through a registry. Stacktraces do not exist yet. The catch "stacktrace"
  variable carries the class atom, so re-raises keep their class
  (`TODO(stacktraces)`).

- **Atoms.** Atoms compiled into the program are static globals in the
  `mana_atoms` linker section. The runtime also has an atom table, so
  `list_to_atom`, `binary_to_atom`, and `binary_to_term` can create atoms at
  run time (`atom_intern`). Atom terms are pointers, so equality is a word
  compare.

- **There IS a GC. Respect the root discipline.** Each process has a heap
  with a copying collector. Any call into compiled code that can allocate is
  a *GC point*. A term in an SSA register across a GC point is a stale
  pointer after the collection. Codegen enforces this with the may-GC effect
  analysis, root frames, and structural spills (see the `mana-codegen` crate
  docs). When you add codegen features, route sibling evaluations through
  `eval_siblings` or `eval_all_rooted`. Never cache a term value across an
  allocation. Functions proven non-allocating are frameless. Do not break
  the conservatism of the effect analysis.

- **ProcCtx words 0, 1, 2** (`heap_top`, `heap_end`, `roots_head`) are a
  fixed contract between `mana-rt` and `mana-codegen`. Compiled code bumps
  the nursery inline through words 0 and 1 and calls `mana_rt_alloc_slow` on
  overflow. Tag `0b111` is the GC forwarding marker. A frame slot that holds
  0 is empty (frames are memset to zero). The collector is generational
  (adaptive nursery plus chunked old space) and relies on term immutability.
  Old objects never point to young ones, so there are no write barriers.
  **Never emit code that mutates the fields of an existing heap term** after
  construction. Change any of this only in lockstep across both crates, and
  run the GC stress program (`Conf.Gc`). `MANA_GC_LOG=1` prints collections.

- **Tail calls are guaranteed (uniform ABI).** Every compiled function has
  the same LLVM prototype, `tailcc i64 f(ctx, x0..x4)`: the six x86-64
  integer registers, never a stack parameter. Calls in tail position are
  `musttail`. Arity over 5 passes the rest through `ProcCtx.argv_spill`
  (word 6), written right before the call and read by the callee prologue
  before anything else. Pointers that escape to the runtime are C wrappers
  (`<sym>.c`). The export table carries `{c_code, fun_code}`. The runtime
  enters fun bodies through the codegen trampoline `mana_call_fun`. Keep all
  of these in lockstep. A C-convention pointer called as tailcc (or the
  reverse) mismatches the callee pop and jumps into garbage. Do not give a
  compiled function a stack parameter. Two real crashes came from that:
  tailcc callee cleanup with a growing musttail chain, and the x86 backend's
  bare `jmp` for a constant stack argument.

- **Integers are exact.** Small integers hold 61 bits. Overflow promotes to
  a bignum through the checked intrinsics. Term comparison (`<`, `==`,
  `=:=`, and friends) follows the full Erlang term order through
  `mana_rt_compare`, with an inline fast path for two small integers.

- `module_info/0,1` and Elixir's `__info__/1` are never compiled in
  practice. Codegen compiles only functions reachable from the entry point.
  Do not remove the reachability pruning. Those generated functions use
  constructs that codegen rejects.

- `examples/erlang/*.core`, `*.beam`, `_mana/`, `_build/`, `deps/`, and
  compiled example binaries are gitignored build artifacts. Never commit
  them.
