# benchmarks

[benchee](https://hex.pm/packages/benchee) suites that run **unchanged** on
both runtimes: compile natively with `mix mana.compile`, run on BEAM with
`mix run`. `make bench` (repo root) runs every suite on both and prints the
two console reports side by side.

    make bench              # all suites, native vs BEAM
    make bench SUITE=Ecto   # one suite

Suites: `Bench.Classic` (fib, list churn, maps, binaries), `Bench.Str`
(unicode/binary string paths), `Bench.Ecto` (the changeset pipeline —
the milestone scoreboard). `Bench.EctoLoop` is the profiling vehicle for
the changeset pipeline: a plain 50k-iteration loop with no benchee
machinery, wired to `make bench-profile` (wall time + callgrind).

Numbers are machine-dependent; the reports are for comparison, not
conformance. Memory/reduction collection stays off (BEAM-internal tracing).

Scoreboard (16-core linux, release runtime vs warm BEAM):

| suite entry | mana | BEAM | |
|---|---|---|---|
| changeset valid | 8.5 µs | 1.7 µs | 2026-08-29, first recorded run |
| changeset valid | 2.9 µs | 1.9 µs | 2026-08-29, after the perf campaign |
| changeset invalid | 2.6 µs | 1.8 µs | 2026-08-29, after the perf campaign |
| query build+inspect | 68 µs | 35 µs | 2026-08-29, Ecto.Query milestone starting number |

The campaign (maps fast paths, frame slimming, static constant binaries,
inline map/binary matching) took the gap from ~5x to ~1.5x; instruction
count on the tight loop fell 5.3x. The remaining gap is spread across
term comparison (`Ecto.Type.equal?`), binary-keyed param maps, and
per-call framing — no single >10% lever left in the profile.
