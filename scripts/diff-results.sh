#!/usr/bin/env bash
# Differential harness: Lean runner output vs committed golden vs Scala CLI
# dump output, three ways, over the corpus.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

shopt -s nullglob
progs=(corpus/programs/*.shl)
if [ ${#progs[@]} -eq 0 ]; then
  echo "diff-results: skipped (corpus is empty until M1)"
  exit 0
fi

mkdir -p .out

( cd lean && lake build shallot-runner >/dev/null && lake exe shallot-runner ../corpus/programs > ../.out/lean.jsonl )
( cd scala && sbt -batch "shallotCli/run dump ../corpus/programs ../.out/scala.jsonl" >/dev/null )

fail=0
if ! diff -u corpus/golden/all.jsonl .out/lean.jsonl; then
  echo "diff-results: Lean output drifted from golden" >&2; fail=1
fi
if ! diff -u corpus/golden/all.jsonl .out/scala.jsonl; then
  echo "diff-results: Scala (extracted) output drifted from golden" >&2; fail=1
fi
[ "$fail" -eq 0 ] && echo "diff-results: OK (Lean ≡ golden ≡ Scala over ${#progs[@]} programs)"
exit "$fail"
