#!/usr/bin/env bash
# Regenerate scala/generated from the Lean sources via the Lens extractor.
# The generated tree is COMMITTED; scripts/check-drift.sh keeps it honest.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

OUT="$PWD/scala/generated/src/main/scala/shallot/gen"

cd lean
lake build Shallot extract

if [ ! -f ../scala/generated/.lens-ready ]; then
  echo "regen: extractor pipeline not established yet (lands in M1) — nothing to do"
  exit 0
fi

lake exe extract --out "$OUT" --pkg shallot.gen
echo "regen: wrote $OUT"
