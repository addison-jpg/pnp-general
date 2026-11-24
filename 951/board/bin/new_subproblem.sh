#!/usr/bin/env bash
# Spin up a new subproblem: its own board branch + its own Lean branch, from templates.
# PRIVATE repo only (remote `work` = addison-jpg/pequalnp-work). Nothing is ever sent to pequalnp.com.
#
#   bin/new_subproblem.sh <ID> <STATEMENT_JSON> [BASE_LEAN_BRANCH]
#     ID              short id, e.g. 612   -> branches board-612 and s612, Lean namespace S612
#     STATEMENT_JSON  cached lemma record with fields id, title, formal_statement, plain_statement
#                     (e.g. work/statements/L-meta-612.json on branch workspace)
#     BASE_LEAN_BRANCH  default coord-951 (has the Lean project, Mathlib pin, kernel, W951 tools)
#
# Run from a clone of addison-jpg/pequalnp-work (or the pequalnp-proofs clone with remote `work`).
# Needs: git, python3, lean toolchain (elan) with the Mathlib cache built under lean/.lake.
set -euo pipefail
ID="$1"; JSON="$2"; BASE="${3:-coord-951}"
NS="S${ID}"; LB="s${ID}"; BB="board-${ID}"
REPO="$(git rev-parse --show-toplevel)"
TMP="$(mktemp -d)"
TITLE=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["title"])' "$JSON")
LID=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["id"])' "$JSON")
STMT=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["formal_statement"])' "$JSON")
PLAIN=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1])).get("plain_statement",""))' "$JSON")
NOW=$(date -u +"%Y-%m-%d %H:%M")
TRAILER=$(printf "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01GmnDhdShHMzucEAq9ottn6")
git -C "$REPO" fetch -q work "$BASE" board

# ---------- 1. Lean branch s<ID>: one module tree, one sorry ----------
git -C "$REPO" worktree add -q "$TMP/lean" "work/$BASE" -b "$LB"
D="$TMP/lean/lean/PEqualNP/$NS"; mkdir -p "$D"
cat > "$D/Statement.lean" <<EOF
import Mathlib
import PEqualNP.Defs

-- $LID: $TITLE
-- The exact statement, copied verbatim from the cached lemma record. Do not edit it.

namespace PEqualNP.Outside.$NS

open PEqualNP.CircuitLowerBounds

/-- The target statement of $LID. -/
def Target : Prop :=
  $STMT

end PEqualNP.Outside.$NS
EOF
cat > "$D/Main.lean" <<EOF
import Mathlib
import PEqualNP.Defs
import PEqualNP.$NS.Statement

namespace PEqualNP.Outside.$NS

/-- THE ONLY SORRY of this subproblem. Shrink it the way W951 did: prove reductions as separate
modules, restate what is left as one named statement, keep exactly one sorry. -/
theorem target : Target := by sorry

end PEqualNP.Outside.$NS
EOF
mkdir -p "$TMP/lean/work"
cat > "$TMP/lean/work/$NS.md" <<EOF
# $NS ($LID) module map
- Statement.lean: \`Target\`, the exact statement (do not edit).
- Main.lean: \`target : Target\`, the only sorry.
Build: \`cd lean && lake build PEqualNP.$NS.Main\` (use your own lean/.lake dir with packages symlinked; see W951 notes).
Reusable from W951 / Kernel: val/step semantics (W951/Eval), sandwich, cones and masks (W951/Cone), merge runs
(W951/MergeRun*), matching and LP duality (Base/Matching/*), kernel circuits (Kernel/*).
EOF
( cd "$TMP/lean" && git add lean/PEqualNP/$NS work/$NS.md && \
  git -c user.name=addison-jpg -c user.email=addison-jpg@users.noreply.github.com commit -q -m "$NS: $LID statement and single-sorry skeleton$TRAILER" )

# ---------- 2. Board branch board-<ID> ----------
git -C "$REPO" worktree add -q --detach "$TMP/board" work/board
B="$TMP/board"
( cd "$B" && git checkout -q --orphan "$BB" && git rm -rqf . && mkdir -p agents research data bin )
git -C "$REPO" show work/board:PROTOCOL.md > "$B/PROTOCOL.md"
git -C "$REPO" show work/board:bin/new_subproblem.sh > "$B/bin/new_subproblem.sh"; chmod +x "$B/bin/new_subproblem.sh"
cat > "$B/BOARD.md" <<EOF
# $LID board (private, addison-jpg/pequalnp-work branch \`$BB\`)

$TITLE

Same rules as the 951 board (PROTOCOL.md): board first, private repo only, models per PROTOCOL, kill stale work.

| Session | Id | Working on | Branch | Last update (UTC) |
|---|---|---|---|---|
| coord | session_01GmnDhdShHMzucEAq9ottn6 | set up; merges and verification | $LB | $NOW |

## PRIORITIES
1. Literature: is $LID known, implied or refuted? (research) -> research/literature.md
2. Small cases by computer (SAT / exhaustive) and counterexample search -> data/, agents/
3. Reductions in Lean, shrinking the single sorry \`target\` (branch $LB, lean/PEqualNP/$NS)
4. Paper draft -> paper.md

## Lean state
- Branch $LB, module tree lean/PEqualNP/$NS. Only sorry: \`target : Target\` in Main.lean.

## Open claims (one line each: what, who, since)

## Free tasks
- Literature pass (priority 1)
- Exhaustive SAT on the smallest instances (priority 2)
- First reduction lemma in Lean (priority 3)
EOF
cat > "$B/paper.md" <<EOF
# $LID: working draft
Status words: proved in Lean / proved on paper / checked on N cases / open / refuted.

## 1. The question
$PLAIN

Formal statement: lean/PEqualNP/$NS/Statement.lean on branch $LB.

## 2. Proved in Lean
(none yet)

## 3. Open core
\`target\` (Main.lean).

## 4. Evidence

## 5. Related work
EOF
cat > "$B/research/literature.md" <<EOF
# $LID literature
Question: is it known, implied, or refuted? Record exact statements + citations; mark what was actually read.
EOF
cat > "$B/README.md" <<EOF
Board for $LID. Lean: branch $LB. Tools available in the private repo:
- Lean 4 + pinned Mathlib (lean/), the W951 library and Kernel (reusable circuit semantics, cones, merges, matching, LP duality)
- python-sat (pip), SAT drivers in tools/stat_search (nb_search.py: edge functions, biclique covers, exact SAT)
- nauty (genbg/geng) for enumerating graphs / set systems when installed
- research: literature notes in research/; use the research session for lookups
EOF
( cd "$B" && git add -A && git -c user.name=addison-jpg -c user.email=addison-jpg@users.noreply.github.com commit -q -m "$BB: board for $LID from template$TRAILER" )

echo "$TMP"
echo "Next: verify (lake build PEqualNP.$NS.Main in $TMP/lean with its own .lake), then push:"
echo "  git -C $TMP/lean push work $LB ; git -C $TMP/board push work $BB"
