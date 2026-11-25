#!/usr/bin/env bash
# One-time setup of a fresh machine/container for this workspace. Run from the repo root.
# Needs network: pequalnp.com, data.pequalnp.com, release(s).lean-lang.org, cache.mathlib.org, github.
set -e
command -v lake >/dev/null 2>&1 || { curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none; }
export PATH="$HOME/.elan/bin:$PATH"
pip install -q python-sat 2>/dev/null || true
cd lean && lake exe cache get && lake build PEqualNP.Defs
echo "ready: Lean + Mathlib cache + PEqualNP.Defs built"
