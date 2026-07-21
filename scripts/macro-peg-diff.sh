#!/usr/bin/env bash
# Differential harness, Macro PEG side: the Lean runner evaluates
# Shallot.MacroPeg.mCases natively; the Scala CLI's `macro-dump` evaluates
# the EXTRACTED table. Both are compared against the committed golden
# (regenerate deliberately via `make corpus-golden`, which also covers this).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

GOLDEN="corpus/golden/macro_peg.jsonl"
if [ ! -f "$GOLDEN" ]; then
  echo "macro-peg-diff: skipped (no golden yet — run 'make corpus-golden')"
  exit 0
fi

mkdir -p .out

( cd lean && lake build mpeg-runner >/dev/null && lake exe «mpeg-runner» ../.out/mpeg-lean.jsonl ) \
  || ( cd lean && lake exe mpeg-runner ../.out/mpeg-lean.jsonl )
( cd scala && sbt -batch "shallotCli/run macro-dump ../.out/mpeg-scala.jsonl" >/dev/null )

fail=0
if ! diff -u "$GOLDEN" .out/mpeg-lean.jsonl; then
  echo "macro-peg-diff: Lean output drifted from golden" >&2; fail=1
fi
if ! diff -u "$GOLDEN" .out/mpeg-scala.jsonl; then
  echo "macro-peg-diff: Scala (extracted) output drifted from golden" >&2; fail=1
fi
n=$(wc -l < "$GOLDEN")
[ "$fail" -eq 0 ] && echo "macro-peg-diff: OK (Lean ≡ golden ≡ Scala over $n cases)"
exit "$fail"
