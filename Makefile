# Shallot + Lens — single verification entry point.
# Fail-fast order: cheap, high-signal steps first.

LAKE_ENV = command -v lake >/dev/null 2>&1 || . $$HOME/.elan/env;

.PHONY: verify verify-fast audit lean lake-test regen check-drift scala diff json-suite macro-peg-diff corpus-golden disksize clean

verify: audit lean lake-test check-drift scala diff json-suite macro-peg-diff
	@echo "== make verify: ALL GREEN =="

# For mid-proof iteration: source audit + proofs only.
verify-fast: audit lean

audit:
	scripts/audit-source.sh

lean:
	cd lean && $(LAKE_ENV) lake build

lake-test:
	cd lean && $(LAKE_ENV) lake test

regen:
	scripts/regen.sh

check-drift:
	scripts/check-drift.sh

scala:
	cd scala && sbt -batch test

diff:
	scripts/diff-results.sh

json-suite:
	scripts/json-suite.sh

macro-peg-diff:
	scripts/macro-peg-diff.sh

corpus-golden:
	scripts/corpus-golden.sh

disksize:
	scripts/disksize.sh

clean:
	cd lean && $(LAKE_ENV) lake clean
	cd scala && sbt -batch clean
