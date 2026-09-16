# Architecture

This document explains the design choices of manallvm and the reasons for
them. It describes the system as it is today. For contributor rules and the
module map of each crate, read `AGENTS.md`.

## What manallvm is

manallvm compiles Erlang and Elixir programs to native binaries. The output
is one static executable. There is no BEAM virtual machine anywhere in the
output. The standard toolchain (`erlc`, `elixirc`)
first lowers source code to Core Erlang. manallvm compiles that Core Erlang
to machine code with LLVM. The binary links against our own runtime, which
is written in Rust.

## The closed world

The compiler knows the whole program at compile time. There is no hot code
loading, no dynamic code loading, and no code server. This choice is the
intended performance advantage over BEAM. It also means some BEAM behavior
cannot exist: `Code.eval_string` has no interpreter, and a module is either
compiled in or absent. A call into an absent module compiles into a loud
abort at that call site. The program fails only if it executes that call.
This copies BEAM, where code with missing modules loads and fails on use.

## The pipeline

The `mix mana.compile` task drives a build in these stages:

1. Mix compiles the project to `.beam` files as usual.
2. The task extracts textual Core Erlang from each beam file. It reads the
   `debug_info` chunk and prints it with `:core_pp`. No source access is
   needed, so hex dependencies work as-is.
3. The task collects the dependency closure. It reads each beam file's
   import table and pulls every imported module in one pass.
4. `manac` (the Rust compiler) parses each `.core` file, finds the code
   that is reachable from the entry point, and compiles one object file
   per module.
5. The C compiler links the objects with the runtime library
   (`libmana_rt.a`) into one binary.

A "chase loop" covers what static analysis cannot see. When manac reports
a module that is only named through a runtime atom (a protocol
implementation, a child spec), the task pulls that module and compiles
again. A manifest file records the final module list, so the next build
runs in one pass.

## Reachability and pruning

manac compiles only the functions that the entry point can reach. Dead
code costs nothing. Dynamic dispatch works through atoms, so the analysis
seeds extra roots:

- A compiled module whose name atom appears in reachable code becomes a
  candidate. If the code also contains a dynamic call, every export of
  that candidate is kept (Elixir modules only).
- A literal `{Module, Function, Args}` tuple keeps that function at every
  arity, because callers extend the argument list at apply time.
- Application modules (given with `--seed-exports`) keep every export once
  they are touched. Configuration and templates call them through atoms
  that no static analysis can see.

## Term representation

The compiler and the runtime agree on the term layout through one crate,
`mana-abi`. It holds the tags, the object kinds, the `ProcCtx` word offsets,
the register count of the calling convention, and the opcode tables of the
runtime entry points. Both sides re-export it, so a number exists in one
place.

A term is one 64-bit word. The low 3 bits are the tag:

| tag   | meaning |
|-------|---------|
| 0b000 | pointer to a boxed object |
| 0b001 | small integer, value = word >> 3 (61 bits) |
| 0b010 | pointer to a static atom |
| 0b011 | nil (`[]`) |
| 0b100 | pointer to a cons cell |
| 0b110 | pid or reference (immediate) |

A boxed object starts with a header word. The low 8 bits of the header
give the kind: tuple (0), float (1), fun (2), bignum (3), map (4), binary
(5), sub-binary view (13). One constraint is easy to miss: a heap header
must never have 0b111 in its low bits. The garbage collector uses that bit
pattern as its forwarding marker. This is why the view kind is 13 and
not 7.

Maps are flat sorted arrays of key-value pairs. Atoms are static globals
that the linker deduplicates, so atom comparison is pointer comparison.

## Integers: smalls and bignums

Small integers hold 61 bits. Arithmetic on two smalls runs inline with an
overflow check. The check uses LLVM overflow intrinsics on the tagged
words directly, so the fast path costs one extra branch and nothing more.
On overflow, a runtime call builds a bignum.

A bignum is a boxed object with sign and 64-bit limbs. Bignums are always
normalized: a value that fits a small is never stored as a bignum. Bignums
allocate in the shared old space with a plain bump allocator. That
allocator can never trigger a collection, so `+`, `-` and `*` are not GC
points. This keeps every arithmetic-heavy function free of GC frames.

The limb arithmetic is hand-written (`crates/mana-rt/src/bigint.rs`). We
measured the `num-bigint` crate against it on our workload shapes. The
crate was 2 to 9 times slower on 1-2 limb values because of conversions at
the term boundary. The comparison benchmark stays in the tree as a test.

## Binaries and sub-binary views

A binary is a boxed object with its bytes inline. Binaries are immutable
after construction. A match like `<<a, rest/binary>>` does not copy the
rest when it is larger than 64 bytes. Instead it creates a view: a small
object that points to the parent binary plus an offset. Views always point
at a root binary, never at another view. Smaller slices copy, so short
binaries never pin a large parent in memory.

A view stores the parent as a term, not as a raw pointer. The parent moves
during collections, so every access recomputes the data pointer. All
runtime code reads binaries through one accessor (`bin_parts`) that
understands both kinds.

## Processes and schedulers

A process is a stackful coroutine (the `corosensei` crate). Schedulers are
OS threads, selected with `MANA_SCHEDULERS=N`. Each process is pinned to
one home scheduler. Only the home thread touches a process's coroutine and
saved state. Another scheduler interacts with a process in three ways
only: push a message, flip its state, wake the thread.

Mailboxes have two parts. Senders push into a lock-free ingress queue. The
receiver drains the ingress into a private list that only the home thread
reads. A send between processes on the same scheduler is zero-copy. A send
across schedulers copies the message into the shared old space first, so
no scheduler ever sees another scheduler's nursery.

One hard rule protects the whole design: a blocking system call must
never run on a scheduler thread. A blocked scheduler cannot reach a
safepoint, and the stop-the-world collector then waits forever.

## Garbage collection

Each scheduler owns a nursery (young heap). All schedulers share one old
space. Minor collections are scheduler-local: they copy live young objects
into the old space. Major collections stop the world and compact the old
space. Compiled functions keep their live terms in root frames, which are
linked stack arrays that the collector walks.

Three rules keep this correct and fast:

- **There is no remembered set.** An old object must never point at a
  young object. The runtime promotes a term before it stores that term
  into old space or into another process.
- **Minors are dirty-tracked.** A parked process is scanned only if it ran
  or received a message since the last minor. Idle supervisors cost
  nothing. This one change took the Phoenix keepalive benchmark from
  630 to 425 microseconds.
- **Eternal objects are scanned once.** Exception reasons live in storage
  that never moves. They are write-once, so one minor scan is enough.
  Majors still walk the full registry.

A whole-program analysis decides which functions can trigger a collection.
Functions that cannot reach an allocation get no frame and no spills. Pure
register code stays pure.

### Memory safety of the runtime

Compiled programs are memory safe by construction: no pointers, no mutable
heap terms, a bounds test and a kind test before every indexed access. The
runtime is not. It manages raw tagged words, and the Rust compiler cannot
see the collector's invariants. The runtime therefore follows the pattern
of the Go runtime: a cheap check that is always on, and a stress mode that
is a knob.

The always-on check runs where the collector already reads an object
header. The kind must be one of the seven valid kinds, and the object must
end before the end of its space. A cons cell must end before the nursery
top. A word with an impossible tag aborts too. On failure the process
exits with code 70 and prints the phase, the address, and the word. This
is the same idea as Go's `found bad pointer in Go heap` throw. It costs a
few compares per copied object.

The stress mode is `MANA_GC_POISON=1`, on by default in debug builds. After
every collection the runtime fills the evacuated memory with a poison word
whose tag is the exception sentinel and whose kind byte is invalid. A stale
pointer then reads poison and the next collection aborts, instead of the
pointer reading a plausible old copy that fails much later. The stress
matrix (`MANA_NURSERY_WORDS=512`, a collection at almost every allocation)
runs with poison on.

A second knob, `MANA_GC_VERIFY=1`, walks the whole reachable heap after
every collection and aborts when a root still reaches an evacuated
nursery, when a header kind is invalid, or when an object runs past its
chunk. This finds a missed root at the collection that missed it. It costs
O(live heap) per collection, so it is off by default, like the verifiers
of Go (`gccheckmark`), HotSpot (`VerifyAfterGC`), and SpiderMonkey (zeal
mode 15).

The invariants that these checks catch, and the remaining gaps against the
Go runtime, are listed in `AGENTS.md`, section "Memory safety".

## BIF cuts

Some OTP modules never compile from beam files. The runtime implements
them natively: `erlang`, `ets`, `file`, `gen_tcp`, `inet`, `crypto`,
`maps`, `io`, `re`, `timer`, and more. We call these "cuts". Two reasons
force this. Some modules bottom out in BEAM C code (NIFs) that does not
exist here. Others, like the file and socket layers, must integrate with
our scheduler rules. The list lives in one place and `manac
--print-bif-modules` prints it, so the build task never drifts from the
compiler.

## Input and output

Sockets are nonblocking everywhere. A dedicated reactor thread runs `mio`
(epoll). When a socket is not ready, the process parks and the reactor
wakes it later through a queue that schedulers drain at safepoints. The
reactor thread never touches process state directly.

File operations use direct blocking system calls. This is a documented
exception to the no-blocking rule and a known debt (`TODO(io-pool)`).
Files are fast because the calls skip BEAM's port machinery: a 1 KB file
round-trip measures about 6 times faster than BEAM.

The runtime also implements streaming zlib on top of the `miniz_oxide`
crate. This gives real DEFLATE compression for HTTP gzip responses and for
WebSocket permessage-deflate. A stream is an opaque `{mana_zlib, N}`
handle, like a socket handle. Compiled Phoenix LiveView applications run
over real WebSockets with this stack.

## Application boot

`mix mana.compile --app` builds a binary that boots like an OTP release.
Nobody writes boot code. The task generates a module at compile time that
does what a release boot script does:

- It bakes the merged compile-time configuration as data, like
  `sys.config`.
- It compiles `config/runtime.exs` into the module, so `System.get_env`
  runs at native boot. `PORT` and `PHX_SERVER` work exactly as in a
  release.
- It starts the application tree in dependency order with direct
  `Module.start/2` calls, read from the `.app` specifications.

Development-only tooling cannot exist in a native binary. The build forces
release semantics: the code reloader and live-reload watchers are compiled
out, and plugs initialize at compile time.

## Compile speed

Warm builds take about one second for a Phoenix-sized program. Three
layers make this possible:

- **An object cache**, content-addressed. The key
  hashes the compiler binary, the `.core` source text, the include set,
  and the effect verdicts of every remote callee. Any input that changes
  the emitted code must be part of the key.
- **Analysis summaries.** A warm build does not parse sources. A summary
  stores what the reachability and effect analyses need per function. The
  compiler re-reads the full AST only when it must compile that module.
- **A build manifest.** It records the final module list of the last
  successful build, so a rebuild starts complete and runs in one compiler
  pass.

## Correctness: BEAM is the oracle

The conformance suite is the gate for every change. Each test program runs
twice: once on BEAM and once as a compiled binary. The two outputs must be
byte-identical. There are no golden files, and a feature without a
conformance program is not done. For changes near the collector or the
schedulers, two more gates apply. The suite runs again with a tiny pinned
nursery (`MANA_NURSERY_WORDS`). An SMP matrix also checks for identical
output at 2, 4, and 8 schedulers.

Benchmarks always compare against a warm BEAM on the same machine, with
the release runtime. The scoreboard lives in `benchmarks/README.md`.

## Dependency policy

Prefer the Rust standard library for anything it covers adequately. Do not
hand-write complex, correctness-critical algorithms that an established
crate provides, unless measurement says otherwise. A new crate must pass
two gates. Its behavior must be identical to BEAM through the conformance
suite. A benchmark must show that it is at least as fast as the code it
replaces.

## Known divergences from BEAM

- `phash2` values differ from BEAM (the hash is internally consistent).
- `is_port/1` returns false for our socket handles.
- The runtime reports local file timestamps as UTC.
- The regex engine is Rust's `regex` crate: no backreferences and no
  lookaround.
- zlib compresses with miniz_oxide, not erlang's zlib. Decompression is
  exact, but compressed bytes differ from BEAM, and the deflate output
  window is always 32K regardless of the requested window bits.
- Bit operations on negative bignums abort (`TODO(bignum-bitops)`).
- Binary segments wider than 64 bits abort (`TODO(bignum-segments)`).
- Process stacks are fixed size (`TODO(stacks)`).
- There is no distribution yet. The design for a Kubernetes-native
  replacement exists, but no code.
