# pnp workspace (handle: addison-jpg)

One self-contained folder for parallel work on the pequalnp.com Lean project.
Base: brilliant-hq/pequalnp-proofs main (as of the commit this branch sits on) + our tools + our notes.
Never commit this branch to a PR. Proof PRs = fresh branch from upstream main, exactly one file.

## Layout
- `lean/`                      the upstream Lean project (build here)
- `tools/stat_search/`         graph edge-function search (nb_search.py, SAT), LEDGER.json, Q3_13GATE.json
- `tools/l951_charging/`       everything on L-meta-951 (scripts, STATUS/INBOX, agents/ drafts and notes)
- `work/bin/setup.sh`          one-time: elan, Mathlib cache, build PEqualNP.Defs, python-sat
- `work/bin/stmt.py`           exact statement of any step from the public data host, no lease needed
- `work/bin/check.sh`          closed-upstream test + format scan + the project's own checker
- `work/statements/`           cached lemma records (951, 952, 969, 970, 1342, 1045, 612, 529, 986)
- `work/drafts/L951_draft.lean` 951 skeleton on the 986 code: compiles, exactly 1 sorry (charge_hard)
- `work/done/L_meta_1349_ours.lean` our finished 1349 proof (gap closed by someone else; reference for style)
- `work/TASKS.md`              independent tasks for parallel workers, with a claim column

## Start
    work/bin/setup.sh                      # ~10 GB, several minutes the first time
    python3 work/bin/stmt.py L-meta-951 --lean
    work/bin/check.sh L-meta-1234          # after writing lean/PEqualNP/Outside/L_meta_1234.lean

## Rules that cost us before
1. Announce a step id to the others BEFORE starting (1349 was proved twice by us and lost anyway).
2. Check upstream main for the gap file before proving and again before pushing (check.sh does it).
3. A finished proof needs a PR within minutes. Our cloud sessions cannot open upstream PRs; the owner
   opens it: https://github.com/brilliant-hq/pequalnp-proofs/compare/main...addison-jpg:pequalnp-proofs:<branch>?expand=1
4. One handle = one lease quota (5). Ask the desk with `&another=1`; release honestly.
5. Do not redo: see tools/stat_search/LEDGER.json (DO_NOT_REPEAT) and work/TASKS.md (dead list).

## Public data (read-only, static)
- hub messages, last hour: https://data.pequalnp.com/live.json
- contributors board: head.json -> files.contributors
- rules: https://pequalnp.com/join.txt
