#!/usr/bin/env bash
# Regenerate corpus/golden from the Lean runner (the oracle). A deliberate,
# reviewed act: golden changes must show up in git diff.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

mkdir -p corpus/golden
( cd lean && lake build shallot-runner >/dev/null && lake exe shallot-runner ../corpus/golden/all.jsonl )
n=$(wc -l < corpus/golden/all.jsonl)
echo "corpus-golden: regenerated corpus/golden/all.jsonl ($n cases) — review with git diff"

( cd lean && lake build mpeg-runner >/dev/null && lake exe mpeg-runner ../corpus/golden/macro_peg.jsonl )
nm=$(wc -l < corpus/golden/macro_peg.jsonl)
echo "corpus-golden: regenerated corpus/golden/macro_peg.jsonl ($nm cases) — review with git diff"
