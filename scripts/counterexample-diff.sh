#!/usr/bin/env bash
# Differential harness, Counterexample side: the Lean runner
# (lean/CounterexampleRunner.lean) evaluates Shallot.MacroPeg.ceCases
# natively; the Scala CLI's `macroPegDiff` module (scala/macro-peg-diff/)
# evaluates the SAME three grammars against the LIVE reference `Evaluator`
# (scala/macro-peg-ref/), independently -- not against extracted code, the
# point of this corpus is cross-checking against the reference
# implementation itself. Both are compared against the committed golden
# (corpus/golden/counterexamples.jsonl; regenerate deliberately by hand,
# mirroring corpus/golden/macro_peg.jsonl -- see scripts/corpus-golden.sh
# for the analogous pattern).
#
# CE-003 (MacroExpander capture bug) has no Lean-side counterpart, so
# there's nothing to golden-compare for it -- we just surface its own
# PASS/FAIL verdict (did the Scala side reproduce the documented bug),
# emitted on stderr by the same `macroPegDiff/run` invocation.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

GOLDEN="corpus/golden/counterexamples.jsonl"
if [ ! -f "$GOLDEN" ]; then
  echo "counterexample-diff: skipped (no golden yet -- create corpus/golden/counterexamples.jsonl)"
  exit 0
fi

mkdir -p .out

( cd lean && lake build counterexample-runner >/dev/null && lake exe counterexample-runner ../.out/ce-lean.jsonl ) \
  || ( cd lean && lake exe counterexample-runner ../.out/ce-lean.jsonl )

( cd scala && sbt -batch "macroPegDiff/run ../.out/ce-scala.jsonl" >/dev/null 2>../.out/ce-scala.stderr )
cat .out/ce-scala.stderr >&2

fail=0
if ! diff -u "$GOLDEN" .out/ce-lean.jsonl; then
  echo "counterexample-diff: Lean output drifted from golden" >&2; fail=1
fi
if ! diff -u "$GOLDEN" .out/ce-scala.jsonl; then
  echo "counterexample-diff: Scala (reference) output drifted from golden" >&2; fail=1
fi

if grep -q "verdict: PASS" .out/ce-scala.stderr; then
  echo "counterexample-diff: CE-003 capture-bug reproduction: PASS"
elif grep -q "verdict: FAIL" .out/ce-scala.stderr; then
  echo "counterexample-diff: CE-003 capture-bug reproduction: FAIL" >&2
  fail=1
else
  echo "counterexample-diff: CE-003 verdict not found in Scala output" >&2
  fail=1
fi

n=$(wc -l < "$GOLDEN")
[ "$fail" -eq 0 ] && echo "counterexample-diff: OK (Lean ≡ golden ≡ Scala over $n cases; CE-003 bug reproduced)"
exit "$fail"
