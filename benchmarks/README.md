# benchmarks

[benchee](https://hex.pm/packages/benchee) suites that run **unchanged** on
both runtimes: compile natively with `mix mana.compile`, run on BEAM with
`mix run`. `make bench` (repo root) runs every suite on both and prints the
two console reports side by side.

    make bench              # all suites, native vs BEAM
    make bench SUITE=Ecto   # one suite

Suites: `Bench.Classic` (fib, list churn, maps, binaries), `Bench.Str`
(unicode/binary string paths), `Bench.Ecto` (the changeset pipeline —
the milestone scoreboard), `Bench.Io` (file round-trips, TCP loopback
echo), `Bench.Http` (compiled Bandit+Plug serving HTTP/1.1), `Bench.Phx`
(the scaffolded Phoenix app's landing page). `Bench.EctoLoop` is the profiling vehicle for
the changeset pipeline: a plain 50k-iteration loop with no benchee
machinery, wired to `make bench-profile` (wall time + callgrind).
`Smoke.Phx` is not a benchmark: 10k keep-alive requests against the
Phoenix landing page, the GC soak test (pairs with `MANA_NURSERY_WORDS`).

Numbers are machine-dependent; the reports are for comparison, not
conformance. Memory/reduction collection stays off (BEAM-internal tracing).

Scoreboard (16-core linux, release runtime vs warm BEAM):

| suite entry | mana | BEAM | |
|---|---|---|---|
| changeset valid | 8.5 µs | 1.7 µs | 2026-08-29, first recorded run |
| changeset valid | 2.9 µs | 1.9 µs | 2026-08-29, after the perf campaign |
| changeset invalid | 2.6 µs | 1.8 µs | 2026-08-29, after the perf campaign |
| query build+inspect | 68 µs | 35 µs | 2026-08-29, Ecto.Query milestone starting number |
| file write+read 1KB | 6.7 µs | 42.9 µs | 2026-08-30, I/O milestone (direct syscalls vs prim_file) |
| file write+read 64KB | 20.8 µs | 48.4 µs | 2026-08-30, I/O milestone |
| tcp connect+echo64+close | 72.9 µs | 106.9 µs | 2026-08-30, I/O milestone |
| http GET, new conn | 192 µs | 260 µs | 2026-08-30, Bandit milestone (mana 1.35x faster) |
| http GET, keepalive | 130 µs | 73 µs | 2026-08-30, Bandit milestone (parsing-bound — sub-binary views are the known lever) |
| phx landing, new conn | 770 µs | 384 µs | 2026-08-31, Phoenix tier-1 first recorded run |
| phx landing, keepalive | 576 µs | 211 µs | 2026-08-31, Phoenix tier-1 first recorded run (render+session+CSRF on top of the Bandit gap) |
| phx landing, new conn | 895 µs | 411 µs | 2026-09-01, after app-boot milestone (full browser path: sessions, gzip, static assets) |
| phx landing, keepalive | 672 µs | 243 µs | 2026-09-01, after app-boot milestone (2.8x behind — sub-binary views remain the lever) |
| phx landing, keepalive | 433 µs | 218 µs | 2026-09-01, perf campaign: dirty-tracked minors (the real lever, found by profiling) + sub-binary views + bignums; 2.8x -> 2.0x |
| phx landing, new conn | 563 µs | 398 µs | 2026-09-01, perf campaign (1.4x behind) |
| str upcase 1KB | 149 µs | 14 µs | 2026-09-01, first recorded — unicode char loop; BEAM match contexts are the known next lever |
| fib 25 | 575 µs | — | 2026-09-01, overflow-checked arith sentinel: no regression vs 618 µs pre-campaign |
| zlib gzip 4KB html | 36.7 µs | 34.4 µs | 2026-09-02, LiveView milestone (real DEFLATE via miniz_oxide — at BEAM parity) |
| zlib gunzip 4KB html | 62.3 µs | 45.9 µs | 2026-09-02, miniz_oxide inflate (1.36x behind zlib — cold path) |
| zlib raw deflate+inflate roundtrip | 41.4 µs | 51.7 µs | 2026-09-02, permessage-deflate shape (mana 1.25x faster) |
| lv event roundtrip (keepalive) | 340 µs | 63 µs | 2026-09-02, LiveView phx-click→diff on a warm socket (5.4x behind — channel + diff + JSON + WS framing per event is the next lever) |
| lv mount+join (new conn) | 3130 µs | 1150 µs | 2026-09-02, full HTTP mount + upgrade + phx_join (2.7x behind) |
| json encode diff (native serde vs Jason) | 1.25 µs | 0.98 µs | 2026-09-02, mana-native JSON — BEAM parity on the LiveView-diff shape, vs 37x behind with mana's compiled Jason (47 µs) |
| json decode diff | 1.61 µs | 1.53 µs | 2026-09-02, mana-native JSON — parity (compiled Jason was 19.5 µs, 12x behind) |
| json encode big | 134 µs | 55 µs | 2026-09-02, 50-key nested (2.4x behind — arbitrary_precision + Value intermediate is the lever; compiled Jason was 1381 µs) |
| json decode big | 123 µs | 94 µs | 2026-09-02, 50-key nested (1.3x behind; compiled Jason was 904 µs) |
| lv event roundtrip (keepalive) | 165 µs | 60 µs | 2026-09-02, server on native JSON (ManaJSON), bench client still on compiled Jason — 5.4x → 2.7x from JSON alone |
| lv event roundtrip (keepalive) | 45 µs | 62 µs | 2026-09-02, **fair client** (client JSON = runtime-selected: serde natively, Jason on BEAM; MANA_SCHEDULERS=1) — **mana 1.4x faster**. Callgrind: the old gap was ~78% the benchmark client's own compiled Jason; the whole server WS path (Bandit framing + channel + serde) is ~5% of instructions |
| lv event roundtrip (keepalive) | 66 µs | 62 µs | 2026-09-02, same, MANA_SCHEDULERS=16 — the three processes (client, transport, channel) land on different schedulers (round-robin, no stealing): cross-thread wakes cost ~20 µs |
| lv mount+join (new conn) | 1750 µs | 1040 µs | 2026-09-02, fair client, schedulers=1 (1.7x behind — the HTTP dead-render path, see phx landing) |
| phx landing (keepalive) | 457 µs | 215 µs | 2026-09-02, re-run, schedulers=1 (2.1x). Callgrind attribution of the native request: Phoenix app 62% (render 20%, session cookie 16%, CSRF 12% — `Base.encode64url` alone 12.8% self), Bandit transport ~13% (adapter header work, date header, `String.downcase` on header tokens; parsing via native decode_packet is <1%), bench client 21%, runtime: minor GC 12.6%, zeroed 64 KiB recv buffers (calloc) 11% |

The campaign (maps fast paths, frame slimming, static constant binaries,
inline map/binary matching) took the gap from ~5x to ~1.5x; instruction
count on the tight loop fell 5.3x. The remaining gap is spread across
term comparison (`Ecto.Type.equal?`), binary-keyed param maps, and
per-call framing — no single >10% lever left in the profile.
