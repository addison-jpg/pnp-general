#!/usr/bin/env bash
# Usage: tools/ath_light/run.sh [branch]   (default origin/refactor/pillars). Needs: git, elan toolchain v4.36.0 (lean, leanexport, nanoda_bin).
set -euo pipefail
B=${1:-origin/refactor/pillars}; W=$(mktemp -d); TC=$(dirname "$(dirname "$(elan which lean)")"); export PATH="$TC/bin:$PATH"
mkdir -p "$W/PEqualNP/W951" "$W/out/PEqualNP/W951"; echo "leanprover/lean4:v4.36.0" > "$W/lean-toolchain"
for m in SearchCheck Asteroid Asteroid_corpus; do git show "$B:one-not/lean/PEqualNP/W951/$m.lean" > "$W/PEqualNP/W951/$m.lean"; done
sed -i 's/^import Mathlib.Tactic.Basic$//' "$W/PEqualNP/W951/SearchCheck.lean"
cd "$W"; for m in SearchCheck Asteroid Asteroid_corpus; do LEAN_PATH=$W/out lean --root=. -o out/PEqualNP/W951/$m.olean PEqualNP/W951/$m.lean; echo "$m compiled (Lean core only)"; done
N=$(grep -oE "^theorem [A-Za-z0-9_]+" PEqualNP/W951/Asteroid_corpus.lean | awk '{print "SearchCheck.Asteroid_corpus."$2}')
LEAN_PATH=$W/out:$TC/lib/lean leanexport PEqualNP.W951.Asteroid_corpus $N > claims.export; ls -la claims.export
printf '{"export_file_path":"%s/claims.export","use_stdin":false,"permitted_axioms":["propext","Quot.sound","Classical.choice","Lean.trustCompiler"],"unpermitted_axiom_hard_error":false,"nat_extension":true,"string_extension":true,"print_success_message":true}' "$W" > nano.json
nanoda_bin nano.json
