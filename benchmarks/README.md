# benchmarks

[benchee](https://hex.pm/packages/benchee) suites that run **unchanged** on
both runtimes: compile natively with `mix mana.compile`, run on BEAM with
`mix run`. `make bench` (repo root) runs every suite on both and prints the
two console reports side by side.

    make bench              # all suites, native vs BEAM
    make bench SUITE=Ecto   # one suite

Suites: `Bench.Classic` (fib, list churn, maps, binaries), `Bench.Str`
(unicode/binary string paths), `Bench.Ecto` (the changeset pipeline —
the milestone scoreboard).

Numbers are machine-dependent; the reports are for comparison, not
conformance. Memory/reduction collection stays off (BEAM-internal tracing).

First recorded run (2026-08-29, 16-core linux, release runtime vs warm BEAM):

| suite entry | mana | BEAM |
|---|---|---|
| changeset valid | 8.5 µs | 1.7 µs |
| changeset invalid | 8.7 µs | 1.7 µs |

The changeset gap (~5x) is the optimization target for the next perf
milestone.
