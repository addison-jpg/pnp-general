# Referee: Theorem G / the U-game (fable-global-price.md §§1–5) — cTAHG, 2026-11-24 (coord 14:00)

**Verdict: CORRECT. Theorem G is PROVED in Lean** (`proofs/w951/PEqualNP/W951/UGame.lean`, gated, std axioms):
`liftSDR_of_ugame`, `no_minCE_of_ugame`, G1 `ugame_of_G1`, G0 `ugame_of_G0`, corollaries (a) `ugame_of_allHeavy`
and (c) `ugame_of_typeB`. The open part is exactly the note's (X): circuits whose lifted outputs LOSE the U-game.
On the barrier suite these are cxMU_dd and cx44_1_junk (the DD core).

## Line-by-line check (paper)
| Item | Status | Note |
|---|---|---|
| (F1) `O_w(x, ν x) = s_w(x)`, monotone in y | correct | `val_lift` + `monoList_lift` |
| (M') a valid class has exactly d_w gates | correct | `card_ltsCls` (≥), `runMT_card_le` (≤) |
| Prop. 1 (a) duality, (b), (c) W(U_L) = MUL, (d) | correct | (c) uses that every valid class ⊆ U_L and has d_w gates |
| Prop. 2 (minimal violator, every gate critical for ≥ 2 sets) | correct | each m_w drops by 0 or 1 when G is removed |
| Theorem U | correct | "at most one atom of t not ≤ ζ'" ⟺ "of two distinct atoms one ≤ ζ'" = hypothesis of `runMT_disjoint_of_le` |
| Lemma N (normal form) | correct | the false coordinates of ζ^ are false at ζ; atoms shrink; certificates persist both ways |
| **Theorem G** | correct | Theorem U per pair + Prop. 1(d); in Lean as `liftSDR_of_ugame` |
| Prop. S (sharpness) | correct | F(ζ') = 0: q_i ≰ ζ' by choice, q'_j ≰ ζ' since O_w'(q'_j) = 1 > O_w'(ζ') |
| G1 validity and certificate | correct | `PureOpt.one`; atom (e_u,1) ≤ (Z_w',1) iff u ∈ Z_w' |
| G0 validity and certificate | correct | `PureOpt.zero` with m_u = A_u (needs h(A_u) = 1 and A_u ∩ S_w ⊆ {u}) |
| Corollaries (a)–(e) | correct | (a), (c) in Lean; (d), (e): S_i \ Z_j = S_i ∩ S_j, A_u ∩ S_j ⊆ {u} |
| Theorem D (i)–(iii) | correct | an atom (A,0) below a zero (Z',1) would force h(Z') = 1; (ii) the swapped zero (top, 0) stays valid since at most one atom has y = 1 |
| Lemma T (T0–T2), odd-cycle corollary | correct | the even 4-cycle example is right: one gate merges all four 2-sets at ζ = 0 |
Wording: §3 "Berge cycles of any parity allowed" is accurate. Theorem G needs no Berge hypothesis, only the won game.

## Barrier suite (CHECKED: `research/one-not/tools/kill_tests/ugame_verify.py`)
Independent of `ugame.solve`, the script re-evaluates the lift, checks validity and separation of every selected system, reruns
the union-find, and checks class size d_w, the certificate and pairwise disjointness.
| Witness | n | s | base | U-game | verified (classes d_w, disjoint, union = base) |
|---|---|---|---|---|---|
| star4, star4b_threshold | 4 | 47 / 14 | 3 | WON | yes |
| pappus_junk_gain | 9 | 66 | 18 | WON | yes |
| match_c_k7, match_s_k7 | 16 | 55 | 23 | WON | yes |
| twin_tree_f2step, twin_tree_N_f2step | 14 | 28 / 30 | 15 | WON | yes |
| nonlocal twin_tree_{or2, e0, and2, maj3} | 14 | 31–35 | 15 | WON | yes |
| cxMU_clean2, cxMU_clean2_DD | 7 | 30 / 33 | 6 | WON | yes |
| tri_all_5593, see_gap_n5, pasch_s14_heavy_atmostone, fano_formula, junk, ess_rand_clean_744 | 5–7 | | | WON | yes |
| **cxMU_dd, cx44_1_junk** | 7 | 36 / 59 | 6 | **LOST** | (the DD core = (X)) |
So the global count route already covers every F2-step counterexample (MATCH-C, the twin trees) and every
real-merge counterexample (STAR4). What is left is (X).

## For the integrator
- MATCH-C refutes the point step but NOT this route: Theorem G gives LiftSDR (MUL) on it.
- `no_minCE_of_ugame` needs the U-game won in a MinCE. (X) is where a proof must use the first-merge structure (Lemma T)
  and, by ElimStep / cTAHG-slack.md, `gates < base` itself. The smallest (X) instance is S = {0,1,2},{0,3,4}, h = x1 ∨ x3.
