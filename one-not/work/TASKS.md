# Parallel tasks (claim by writing your session/worker name in the last column, then push)

State as of 2026-11-23 ~22:50 UTC. Credited steps for addison-jpg: 0.

| # | Task | Kind | Input | Done when | Claimed by |
|---|------|------|-------|-----------|------------|
| 1 | L-meta-951 `charge_hard` | proof (hard, open) | work/drafts/L951_draft.lean, tools/l951_charging/agents/MATH_FINDINGS.md, INBOX.json | the 1 sorry is gone and check.sh accepts | front (math), scaffold (data) |
| 2 | 951: Wegener 6.6 / Mehlhorn top-down AND-elimination with one NOT | proof idea | scaffold's LIT #2 note (step (iii) breaks only when a in {h=0}, b in {h=1}) | a written argument for the mixed-side case, or a counterexample circuit | scaffold |
| 3 | 951: C1 lemma falsification at base+2 | SAT search | tools/l951_charging/live951.py (build_live: NOT must be in an output cone) | remaining cells (Pasch p>=4, Fano, n=8) SAT/UNSAT | front |
| 4 | Fano 13 gates, <=1 NOT | SAT search (refutes 951 if SAT) | tools/l951_charging/fano_cells_scaffold.py | all 13 cells decided | scaffold |
| 5 | Q3 at 12 gates | SAT search | `python3 tools/stat_search/nb_search.py graph q3 --sat 12 --timeout 3000` | SAT => opt 12, UNSAT => 13-gate circuit optimal | free (coord's run died with its session) |
| 6 | L-meta-1342 shard 21 | desk SEARCH step | lease held by front | witness file or `exhausted` release with program sha256 | front |
| 8 | L-meta-1045 (C4-free weighted count) | proof (open, no argument held) | work/statements/L-meta-1045.json; notes below | proof or counterexample | free |
| 9 | L-meta-612 (C4-free >= E + tau - 1) | proof (open) | work/statements/L-meta-612.json | proof | free |

## Notes worth keeping
- 951 principle: the only NOT is N = not h, h monotone. Every wire equals C0 on {h=1} and C1 on {h=0}
  (NOT replaced by 0 / 1), both monotone, C0 <= C1.
- 951 P-scheme: for a hard set S (h(Z_S)=1) take a minterm M of h avoiding S; test points 1_M + e_x give
  >= |S|-1 merges, the NOT is never one. Shared merges hard-hard need M_a cap S_b and M_b cap S_a nonempty;
  easy-hard is not excluded in this scheme.
- 1045: every edge is born at an AND gate g = a AND b with u in s(a)\s(b), v in s(b)\s(a) (s = unit vectors
  the wire accepts); the narrow walk from the output has at most (#narrow OR + 1) leaves. Missing: tying
  |E| to #AND + #wide OR.

## Dead / do not repeat
- L-meta-969 as posted (<= 11 gates for Q3) is false: 970 (>= 12) is checked. No Lean file from the 13-gate circuit.
- 951 Lemma R (restrict a minterm to 1) is false as stated; most early test circuits had a dead NOT.
- Closed upstream: 986, 970, 1003, 701, 1349 (GravityLizard #2746), 1375 (Robert Cass #2752).
- Tree search at Q3 scale: use SAT.
