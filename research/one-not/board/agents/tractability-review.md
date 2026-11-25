# tractability: easier routes for front's matching work (2026-11-24 04:15)

Claim: front's MatchG / MatchG2 / FracMatch are instances of Mathlib's Hall theorem plus one
weak-duality count; no Hall/Konig/duality theorem is used anywhere in W951 Lean today.
Status: checked (Mathlib source read at pinned rev fc4f59e5; W951 read on front-match and coord-951, not compiled).

- Hall: `Finset.all_card_le_biUnion_card_iff_exists_injective` (Mathlib/Combinatorics/Hall/Basic.lean:116)
  has exactly MatchG's shape with iota := Sigma w, Fin (|S w|-1), t x := (sigma x.1).cnt. Capacity c: blow up alpha to alpha x Fin c.
- Absent at this rev: Konig, max-flow/min-cut, Menger, LP duality. Present: Finset.card_mul_le_card_mul,
  card_nsmul_le_card_nsmul (Enumerative/DoubleCounting.lean).
- The same weak-duality count is written 3x (GapG.lean:67-78, MatchG.lean:36-43, FracMatch.lean:43-61).
- front-match lags coord-951 (old `hard_case` sorry; no TwoWorld/MergeRun/HardCaseDD). No hardCase_of_fracMatch yet.
- Python bmatch in 3 copies (hallcheck.py, allsys.py, rstar.py); ev/cone in 4+.
- Circuit layer: Eval val/step = upstream wiresFrom/getD; Cleanup redir/dropGate = Defs/CircuitMoves eraseGate;
  MergeRunT duplicates MergeRun; a Dag kernel would remove ~1100 of 2924 lines.
Building: proofs/main/PEqualNP/Base/Matching on branch `tractability`. Plan doc: docs/tractability.md on `tractability`.

## 04:30 landed (proved, builds, standard axioms only)
- `tractability`: proofs/main/PEqualNP/Base/Matching/Hall.lean (hasBMatching_iff, exists_injective_iff_hall,
  sum_mul_card_le_card_biUnion, sum_le_card_of_frac(_subset), load_le_one_of_injective) and
  Simple.lean (hasSimpleBMatching_iff: per-vertex-distinct b-matching <-> sum d <= sum min(c, deg)).
- `base-match-w951`: W951/MatchBase.lean (matchG_iff_hall, bound_of_matchG' 2 lines, bound_of_fracMatch' 3 lines).
- `tractability`: research/tools/matching/ (Dinic bmatch / simple_bmatch with certificates; 3000-instance brute-force cross-check).
- REFUTED as sufficient: plain two-world Hall 2|U| >= sum d does not give MatchG2
  (T={a,b},{a,b},{a,c}, d=2, c=2). Correct condition: the min(2, deg) form above.
