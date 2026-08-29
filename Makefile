BIN := $(CURDIR)/target/debug/manac

.PHONY: build test test-conformance example-elixir bench bench-profile build-release

build:
	cargo build

test:
	cargo test

# BEAM-as-oracle conformance suite — the correctness gate.
test-conformance: build
	cd test/conformance && MANA_BIN=$(BIN) mix test

# run every benchmark suite natively and on BEAM; SUITE=Classic|Str|Ecto
SUITE ?= Classic Str Ecto
bench: build-release
	@cd benchmarks && for s in $(SUITE); do \
	  echo "==== Bench.$$s (mana) ===="; \
	  MANA_BIN=$(RBIN) mix mana.compile --entry Bench.$$s.run/0 --out /tmp/mana_bench_$$s >/dev/null && /tmp/mana_bench_$$s/app; \
	  echo "==== Bench.$$s (BEAM) ===="; \
	  mix run --no-start -e "Bench.$$s.run()"; \
	done

# tight-loop changeset profile: wall time + callgrind attribution (release runtime)
bench-profile: build-release
	@cd benchmarks && \
	  MANA_BIN=$(RBIN) mix mana.compile --entry Bench.EctoLoop.run/0 --out /tmp/mana_ecto_loop >/dev/null && \
	  echo "==== wall (mana) ====" && /tmp/mana_ecto_loop/app && \
	  echo "==== wall (BEAM) ====" && mix run --no-start -e "Bench.EctoLoop.run()" && \
	  echo "==== callgrind ====" && \
	  valgrind --tool=callgrind --callgrind-out-file=/tmp/cg_ecto_loop.out /tmp/mana_ecto_loop/app >/dev/null && \
	  callgrind_annotate --threshold=80 /tmp/cg_ecto_loop.out | head -50

build-release:
	cargo build --release

RBIN := $(CURDIR)/target/release/manac

example-elixir: build
	cd examples/elixir/fib && MANA_BIN=$(BIN) mix mana.compile --entry Fib.main/0 && ./_mana/app
