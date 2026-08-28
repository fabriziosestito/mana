BIN := $(CURDIR)/target/debug/manac

.PHONY: build test test-conformance example-elixir

build:
	cargo build

test:
	cargo test

# BEAM-as-oracle conformance suite — the correctness gate.
test-conformance: build
	cd test/conformance && MANA_BIN=$(BIN) mix test

example-elixir: build
	cd examples/elixir/fib && MANA_BIN=$(BIN) mix mana.compile --entry Fib.main/0 && ./_mana/app
