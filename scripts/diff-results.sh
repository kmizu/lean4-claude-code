#!/usr/bin/env bash
# Differential harness: the Lean runner evaluates Shallot.cases natively;
# the Scala CLI's `dump` evaluates the EXTRACTED table. Both are compared
# against the committed golden (regenerate deliberately via `make corpus-golden`).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

GOLDEN="corpus/golden/all.jsonl"
if [ ! -f "$GOLDEN" ]; then
  echo "diff-results: skipped (no golden yet — run 'make corpus-golden')"
  exit 0
fi

mkdir -p .out

( cd lean && lake build shallot-runner >/dev/null && lake exe «shallot-runner» ../.out/lean.jsonl ) \
  || ( cd lean && lake exe shallot-runner ../.out/lean.jsonl )
( cd scala && sbt -batch "shallotCli/run dump ../.out/scala.jsonl" >/dev/null )

fail=0
if ! diff -u "$GOLDEN" .out/lean.jsonl; then
  echo "diff-results: Lean output drifted from golden" >&2; fail=1
fi
if ! diff -u "$GOLDEN" .out/scala.jsonl; then
  echo "diff-results: Scala (extracted) output drifted from golden" >&2; fail=1
fi
n=$(wc -l < "$GOLDEN")
[ "$fail" -eq 0 ] && echo "diff-results: OK (Lean ≡ golden ≡ Scala over $n cases)"
exit "$fail"
