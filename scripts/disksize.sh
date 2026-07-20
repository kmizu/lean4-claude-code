#!/usr/bin/env bash
# Disk hygiene report — the host disk sits at ~95%, keep an eye on it.
set -uo pipefail
cd "$(dirname "$0")/.."
echo "== disk =="
df -h / | tail -1
echo "== project & tool caches =="
du -sh "$HOME/.elan" lean/.lake scala/target scala/*/target "$HOME/.cache/coursier" "$HOME/.sbt" 2>/dev/null || true
