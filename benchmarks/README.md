# benchmarks

[benchee](https://hex.pm/packages/benchee) suites that run **unchanged** on
both runtimes. Compile them natively with `mix mana.compile`. Run them on BEAM
with `mix run`. `make bench` (repository root) runs every suite on both
runtimes and prints the two console reports side by side.

    make bench              # all suites, native vs BEAM
    make bench SUITE=Ecto   # one suite

Suites:

- `Bench.Classic` — fib, list churn, maps, binaries.
- `Bench.Str` — unicode and binary string paths.
- `Bench.Ecto` — the changeset pipeline (the milestone scoreboard).
- `Bench.Io` — file round trips, TCP loopback echo.
- `Bench.Http` — compiled Bandit plus Plug, HTTP/1.1.
- `Bench.Phx` — the landing page of the scaffolded Phoenix app.
- `Bench.Zlib`, `Bench.Ws`, `Bench.Json` — compression, LiveView over
  WebSocket, JSON encode and decode.

`Bench.EctoLoop` is the profiling vehicle for the changeset pipeline: a plain
50k-iteration loop without benchee, wired to `make bench-profile` (wall time
plus callgrind). `Smoke.Phx` is not a benchmark. It sends 10k keep-alive
requests to the Phoenix landing page. It is the GC soak test and pairs with
`MANA_NURSERY_WORDS`.

Numbers are machine-dependent. The reports are for comparison, not for
conformance. Memory and reduction collection stay off (BEAM-internal
tracing).

Scoreboard (16-core Linux, release runtime vs warm BEAM):

| suite entry | mana | BEAM | note |
|---|---|---|---|
| changeset valid | 8.5 µs | 1.7 µs | 2026-08-29, first recorded run |
| changeset valid | 2.9 µs | 1.9 µs | 2026-08-29, after the perf campaign |
| changeset invalid | 2.6 µs | 1.8 µs | 2026-08-29, after the perf campaign |
| query build+inspect | 68 µs | 35 µs | 2026-08-29, Ecto.Query milestone, starting number |
| file write+read 1KB | 6.7 µs | 42.9 µs | 2026-08-30, I/O milestone. Direct syscalls vs prim_file |
| file write+read 64KB | 20.8 µs | 48.4 µs | 2026-08-30, I/O milestone |
| tcp connect+echo64+close | 72.9 µs | 106.9 µs | 2026-08-30, I/O milestone |
| http GET, new conn | 192 µs | 260 µs | 2026-08-30, Bandit milestone. mana 1.35x faster |
| http GET, keepalive | 130 µs | 73 µs | 2026-08-30, Bandit milestone. Parsing-bound. Sub-binary views are the known lever |
| phx landing, new conn | 770 µs | 384 µs | 2026-08-31, Phoenix tier 1, first recorded run |
| phx landing, keepalive | 576 µs | 211 µs | 2026-08-31, Phoenix tier 1, first recorded run. Render, session, and CSRF on top of the Bandit gap |
| phx landing, new conn | 895 µs | 411 µs | 2026-09-01, after the app-boot milestone. Full browser path: sessions, gzip, static assets |
| phx landing, keepalive | 672 µs | 243 µs | 2026-09-01, after the app-boot milestone. 2.8x behind. Sub-binary views remain the lever |
| phx landing, keepalive | 433 µs | 218 µs | 2026-09-01, perf campaign. Dirty-tracked minors (the real lever, found by profiling), sub-binary views, bignums. 2.8x to 2.0x |
| phx landing, new conn | 563 µs | 398 µs | 2026-09-01, perf campaign. 1.4x behind |
| str upcase 1KB | 149 µs | 14 µs | 2026-09-01, first recorded. Unicode char loop. BEAM match contexts are the known next lever |
| fib 25 | 575 µs | — | 2026-09-01, overflow-checked arithmetic sentinel. No regression vs 618 µs before the campaign |
| zlib gzip 4KB html | 36.7 µs | 34.4 µs | 2026-09-02, LiveView milestone. Real DEFLATE with miniz_oxide, at BEAM parity |
| zlib gunzip 4KB html | 62.3 µs | 45.9 µs | 2026-09-02, miniz_oxide inflate. 1.36x behind zlib, cold path |
| zlib raw deflate+inflate roundtrip | 41.4 µs | 51.7 µs | 2026-09-02, permessage-deflate shape. mana 1.25x faster |
| lv event roundtrip (keepalive) | 340 µs | 63 µs | 2026-09-02, LiveView phx-click to diff on a warm socket. 5.4x behind. Channel, diff, JSON, and WS framing per event are the next lever |
| lv mount+join (new conn) | 3130 µs | 1150 µs | 2026-09-02, full HTTP mount, upgrade, and phx_join. 2.7x behind |
| json encode diff (native serde vs Jason) | 1.25 µs | 0.98 µs | 2026-09-02, mana-native JSON. BEAM parity on the LiveView-diff shape. Compiled Jason was 47 µs, 37x behind |
| json decode diff | 1.61 µs | 1.53 µs | 2026-09-02, mana-native JSON, parity. Compiled Jason was 19.5 µs, 12x behind |
| json encode big | 134 µs | 55 µs | 2026-09-02, 50-key nested. 2.4x behind. The arbitrary_precision Value intermediate is the lever. Compiled Jason was 1381 µs |
| json decode big | 123 µs | 94 µs | 2026-09-02, 50-key nested. 1.3x behind. Compiled Jason was 904 µs |
| lv event roundtrip (keepalive) | 165 µs | 60 µs | 2026-09-02, server on native JSON (ManaJSON), bench client still on compiled Jason. 5.4x to 2.7x from JSON alone |
| lv event roundtrip (keepalive) | 45 µs | 62 µs | 2026-09-02, **fair client** (client JSON is runtime-selected: serde natively, Jason on BEAM), MANA_SCHEDULERS=1. **mana 1.4x faster.** Callgrind: about 78% of the old gap was the compiled Jason of the benchmark client. The whole server WS path (Bandit framing, channel, serde) is about 5% of instructions |
| lv event roundtrip (keepalive) | 66 µs | 62 µs | 2026-09-02, same, MANA_SCHEDULERS=16. The three processes (client, transport, channel) land on different schedulers (round-robin, no stealing). Cross-thread wakes cost about 20 µs |
| lv mount+join (new conn) | 1750 µs | 1040 µs | 2026-09-02, fair client, schedulers=1. 1.7x behind. The HTTP dead-render path, see phx landing |
| phx landing (keepalive) | 457 µs | 215 µs | 2026-09-02, re-run, schedulers=1, 2.1x. Callgrind attribution of the native request: `Base.url_encode64` **37% inclusive** (6 calls per request: session cookie plus CSRF token signing). Not the encoder itself: the `element(i, {4096 chars})` table literal was heap-allocated at each use (4097 words × 4 per 6 input bytes), which also drove most of the minor-GC share (12%). Zeroed 64 KiB recv buffers 11%. Bandit transport about 13% (adapter header work, parsing is native decode_packet, under 1%) |
| phx landing (keepalive) | 431 µs | 215 µs | 2026-09-02, per-thread recv scratch. No 64 KiB calloc per read |
| phx landing (keepalive) | **194 µs** | 215 µs | 2026-09-03, **constant tuples, lists, and floats compile to static terms** (codegen). The Base table literal is built once at link time. 2.2x faster. **mana 1.1x ahead of BEAM.** `Base.url_encode64` 200 B: 152 to 1.7 µs (BEAM 1.05) |
| phx landing (new conn) | **300 µs** | 401 µs | 2026-09-03, same. mana 1.3x ahead |
| lv event roundtrip (keepalive) | **35 µs** | 62 µs | 2026-09-03, same. mana 1.8x ahead (fair client, schedulers=1) |
| lv mount+join (new conn) | **888 µs** | 1040 µs | 2026-09-03, same. mana 1.2x ahead (was 1.7x behind) |
| phx landing (keepalive) | **180 µs** | 215 µs | 2026-09-03, inline `rest::binary` views (no bin_slice call or copy) plus zero-copy `binary:split` (parts are views, not copies) |
| str upcase 1KB | 80 µs | 14 µs | 2026-09-03, inline rest views (was 149) |
| str upcase 1KB | **26.6 µs** | 14 µs | 2026-09-03, **case pre-dispatch switch**. String.Unicode.upcase/3 has about 1400 byte-prefix clauses. One `switch` on the first byte replaces the sequential prefix compares. 5.6x total in this series. The rest is the per-byte view plus cons allocation. A match-context shape removes the view |
| str split+join | 13.6 µs | 9.2 µs | 2026-09-03, zero-copy split (was 18.9) |
| changeset valid | **2.4 µs** | 1.9 µs | 2026-09-03, case pre-dispatch (clause tables everywhere) |
| phx landing (keepalive) | **128 µs** | 215 µs | 2026-09-04, receive-timeout cursor reset (BEAM save-pointer semantics, Bandit no longer leaks one `{:plug_conn,:sent}` per request) plus **guaranteed tail calls** (uniform all-register tailcc ABI plus musttail). The earlier "1 ms stall" was a SIGSEGV: gen_server:loop/7 was a real call that leaked about 3 KB of stack per message. Every long-lived gen_server died after about 80k messages |
| http GET, keepalive | **43 µs** | 72 µs | 2026-09-04, same (was 125). 8 of 8 runs, at 1 and 16 schedulers |
| gen_server 2M messages | 5.1 s, 25 MB | — | 2026-09-04, tailcc plus VecDeque mailbox. Before: SIGSEGV at about 80k, then O(N) `Vec::remove(0)` per receive under backlog |
| fib 25 | 624 µs | — | 2026-09-04, register shuffle cost of the uniform ABI (was 575) |
| changeset valid | 2.6 µs | 1.9 µs | 2026-09-04, same ABI cost (was 2.2). The correctness fix outranks it. The arity>5 spill is the lever if it matters |

The campaign (maps fast paths, frame slimming, static constant binaries,
inline map and binary matching) took the gap from about 5x to about 1.5x.
The instruction count on the tight loop fell 5.3x. The remaining gap is
spread across term comparison (`Ecto.Type.equal?`), binary-keyed parameter
maps, and per-call framing. No single lever over 10% is left in the profile.
