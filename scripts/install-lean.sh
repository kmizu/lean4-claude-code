#!/usr/bin/env bash
# Idempotent elan + pinned Lean toolchain installer.
set -euo pipefail

TOOLCHAIN="leanprover/lean4:v4.32.0"

if [ ! -x "$HOME/.elan/bin/elan" ]; then
  echo "==> Installing elan (no default toolchain)"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh \
    || curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
else
  echo "==> elan already installed"
fi

export PATH="$HOME/.elan/bin:$PATH"

if ! elan toolchain list | grep -q "${TOOLCHAIN#leanprover/}"; then
  echo "==> Installing toolchain $TOOLCHAIN"
  elan toolchain install "$TOOLCHAIN"
else
  echo "==> Toolchain $TOOLCHAIN already installed"
fi

# Ensure zsh picks up elan on interactive shells.
if [ -f "$HOME/.zshrc" ] && ! grep -q '.elan/env' "$HOME/.zshrc"; then
  printf '\n. "$HOME/.elan/env"\n' >> "$HOME/.zshrc"
  echo "==> Added elan to ~/.zshrc"
fi

elan --version
elan toolchain list
