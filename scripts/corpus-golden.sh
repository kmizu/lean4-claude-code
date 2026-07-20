#!/usr/bin/env bash
# Regenerate corpus/golden from the Lean runner (the oracle). A deliberate,
# reviewed act: golden changes must show up in git diff.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

shopt -s nullglob
progs=(corpus/programs/*.shl)
if [ ${#progs[@]} -eq 0 ]; then
  echo "corpus-golden: skipped (corpus is empty until M1)"
  exit 0
fi

mkdir -p corpus/golden
( cd lean && lake build shallot-runner >/dev/null && lake exe shallot-runner ../corpus/programs > ../corpus/golden/all.jsonl )
echo "corpus-golden: regenerated corpus/golden/all.jsonl — review with git diff"
