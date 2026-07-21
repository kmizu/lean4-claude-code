#!/usr/bin/env bash
# JSONTestSuite conformance + differential check:
#   1) the verified parser (Lean-native) and the EXTRACTED parser (Scala)
#      must produce IDENTICAL verdicts over the vendored corpus;
#   2) y_ files must all be accepted, n_ files must all be rejected
#      (i_ files are implementation-defined; ours rejects lone surrogates).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v lake >/dev/null 2>&1 || . "$HOME/.elan/env"

mkdir -p .out
( cd lean && lake build json-suite >/dev/null && lake exe json-suite ../corpus/json ../.out/json-lean.jsonl )
( cd scala && sbt -batch "shallotCli/run json-suite ../corpus/json ../.out/json-scala.jsonl" >/dev/null )

if ! diff -u .out/json-lean.jsonl .out/json-scala.jsonl; then
  echo "json-suite: DIFF — extracted parser disagrees with the verified one" >&2
  exit 1
fi

bad_y=$(grep '"file":"y_' .out/json-lean.jsonl | grep -cv '"verdict":"accept"' || true)
bad_n=$(grep '"file":"n_' .out/json-lean.jsonl | grep -c '"verdict":"accept"' || true)
total=$(wc -l < .out/json-lean.jsonl)
if [ "$bad_y" != "0" ] || [ "$bad_n" != "0" ]; then
  echo "json-suite: EXPECTATION FAILURE (y_ rejected: $bad_y, n_ accepted: $bad_n)" >&2
  exit 1
fi
echo "json-suite: OK ($total files, Lean ≡ Scala, y_/n_ all as required)"
