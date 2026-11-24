#!/usr/bin/env bash
# Concatenate the W951 development (plus the kernel files it imports) into ONE Lean file whose only
# imports are Mathlib and PEqualNP.Defs. Each source file keeps its own namespace/section/open lines;
# only `import` lines are dropped. Order = a topological order of the imports.
#   work/bin/merge951.sh [OUT]   (default lean/PEqualNP/Outside/L_meta_951.lean)
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
out="${1:-lean/PEqualNP/Outside/L_meta_951.lean}"
L="$root/lean/PEqualNP"
FILES="Kernel/GateShape W951/Eval Kernel/W951Extra Kernel/Circuit Kernel/W951Core W951/MergeRunT W951/Count W951/Frame W951/Cleanup W951/Charge Base/Matching/Hall W951/Cone W951/GapG W951/Cases W951/Small3 W951/TwoWorld W951/Hard W951/Main Kernel/W951Off W951/Restrict W951/Dead W951/Lower W951/Core W951/MinCE W951/MinCEFacts W951/MinCEN3 W951/Final"
mkdir -p "$(dirname "$out")"
{
  printf 'import Mathlib\nimport PEqualNP.Defs\n\n'
  for f in $FILES; do
    printf -- '-- ===== %s.lean =====\n' "$f"
    grep -v '^import ' "$L/$f.lean" | cat -s
    echo
  done
} > "$out"
