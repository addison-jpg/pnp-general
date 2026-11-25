#!/usr/bin/env bash
# Check one proof file the way upstream does. Run from the repo root.
#   work/bin/check.sh L-meta-1234        (file must be at proofs/main/PEqualNP/Outside/L_meta_1234.lean)
# 1. closed upstream already?  2. format scan  3. the project's own checker with the public statement.
set -e
export PATH="$HOME/.elan/bin:$PATH"
ID="$1"; F="proofs/main/PEqualNP/Outside/$(echo "$ID" | tr '-' '_').lean"
[ -f "$F" ] || { echo "no file $F"; exit 2; }
git fetch -q https://github.com/brilliant-hq/pequalnp-proofs main 2>/dev/null && \
  git cat-file -e FETCH_HEAD:"$F" 2>/dev/null && { echo "CLOSED UPSTREAM: $F is already on brilliant-hq main. Stop."; exit 4; }
for w in sorry native_decide '"' 'set_option' 'macro' 'notation' 'initialize' 'elab '; do
  grep -n -F -- "$w" "$F" | head -3 | sed "s/^/FORMAT? [$w] /"; done
python3 work/bin/stmt.py "$ID" --lean > "/tmp/$ID.statement"
node research/tools/check-lean.mjs "$F" "/tmp/$ID.statement" check | tail -3
