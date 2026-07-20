#!/usr/bin/env bash
# Fail if the committed scala/generated tree differs from a fresh extraction.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

GEN="scala/generated/src/main/scala/shallot/gen"

if [ ! -f scala/generated/.lens-ready ]; then
  echo "check-drift: skipped (extractor pipeline not established until M1)"
  exit 0
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

( cd lean && lake build Shallot extract >/dev/null && lake exe extract -- --out "$tmp" --pkg shallot.gen )

if ! diff -ru "$tmp" "$GEN"; then
  echo "check-drift: DRIFT — committed generated code is stale. Run 'make regen' and review the diff." >&2
  exit 1
fi
echo "check-drift: OK (committed generated code matches fresh extraction)"
