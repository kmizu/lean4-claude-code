#!/usr/bin/env bash
# Zero-sorry policy enforcement: fail if forbidden constructs appear in Lean
# sources. `native_decide` is banned because it moves trust to the compiler;
# `axiom` because all proofs must rest on the standard axioms only.
set -euo pipefail
cd "$(dirname "$0")/.."

targets=()
for d in lean/Shallot lean/Lens lean/LensTest; do
  [ -d "$d" ] && targets+=("$d")
done
for f in lean/Shallot.lean lean/Lens.lean lean/Audit.lean lean/Runner.lean lean/LensTests.lean; do
  [ -f "$f" ] && targets+=("$f")
done

hits=$(grep -rnE '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' "${targets[@]}" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "audit-source: FORBIDDEN constructs found:" >&2
  echo "$hits" >&2
  exit 1
fi
echo "audit-source: OK (no sorry/admit/native_decide/axiom)"
