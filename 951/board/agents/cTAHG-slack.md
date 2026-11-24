# What `gates < base` buys at a non-local cube (cTAHG, 2026-11-24, coord 13:48 (b))

Words: PROVED = Lean, gated; CHECKED = computed; TESTED = computed on the local corpora only.

## 1. MATCH-C (k = 7): slack and where it sits (CHECKED, tools/kill_tests/elim_vs_gain.py)
s = 55, base = 23, s − base = 32 = 4k + 4; |F2(∅)| − base = 15 = 2k + 1; the F2 step fails by 1 at every point.
The surplus is exactly the junk layer plus the NOT gadget. A base-size circuit deletes:
- j_i, j'_i, p_i, p'_i (4k gates; e_i = x_{u_i} ∨ x_{a_i} and the trees run over the inputs);
- h, N and the two ANDs X_A ∧ N, X_B ∧ N (4 gates);
then o_A = f_A ∨ x_y and o_B = f_B ∨ x_{y'}, giving 2(k − 1) + 2 + k + 2 = 3k + 2 = base.
Per point at Q = ∅ (v | cost | gain | elim1 | surviving F2 losers):
- u_i, a_i: cost 8–9, gain 6–8, elim1 16–17, surv 0;
- y, y': cost 8, gain 2, elim1 18, surv 0.
Here elim1(v) = gates removed by x_v := 1 (constants, input copies, duplicate functions, dead wires).
So x_v := 1 ELIMINATES about twice the cost at every v, while the F2 gain stays below the cost: every F2 gate that leaves F2 is also an eliminated gate.

## 2. The transfer (PROVED; ElimStep.lean)
Lex-minimality makes every proper subfamily, computed by a correct circuit with ≤ s gates, a NON-counterexample (`MinCE.sub_bound`). Hence, in a MinCE with deficit δ = base − s ≥ 1:
- `MinCE.elim_lt`: elim1(v) ≤ s − base({v}) = cost(v) − δ at EVERY v (also for any restriction / output deletion).
- An F2 step at v needs gain(v) ≥ cost(v), so at least δ + (s1(v) − base({v})) ≥ δ F2 gates must leave F2 WITHOUT being eliminated (gain ≤ elim1 + surv). This is the exact deficiency transfer: the deficit must be carried by surviving F2 losers.
- `no_minCE_of_elimStep`: ONE elimination step at the top closes 951. It asks for a proper subfamily (e.g. the sets not through v) with a correct circuit of ≤ s − ∑_{removed} d_w gates. The induction below the top is free by minimality; at Q ≠ ∅ the size count s_Q ≥ base(Q) holds by `sub_bound`.

## 3. Data (TESTED: 104 correct one-NOT circuits in the repo, n ≤ 16; `elim_vs_gain.py --corpus`)
- Elimination step GE (some v with elim1(v) ≥ cost(v)) at Q = ∅: 104 / 104, including MATCH-C, TWIN-TREE(-N) and the n = 14 twin variants, where the F2 step fails. Smallest margin max_v (elim1 − cost) = 3 on the 22-circuit witness set.
- The F2 step without GE: 0. GE without the F2 step: 8. On this data the F2 step is strictly STRONGER than GE.
- F2 losers that survive the restriction (gain beats elimination): 54 of 1,252 (circuit, Q, v) rows, e.g. tri_all_5593 at v = 2: gain 4 = cost, elim1 2. MATCH-C has none.

## 4. Heredity (question (3))
- `MinCE.heredity` / `heredity_multi` are x := 0 (deletion): elim0(v) ≤ deg(v).
- `MinCE.outDel` (MinCEFacts) is x := 1 with DEAD gates only.
- `MinCE.sub_bound` / `MinCE.elim_lt` (new) are the full x := 1 form for any correct circuit of the subfamily, with constants, copies and duplicates counted too.
- Earlier notes (work/notes951/hard_induction.md, 'variable-fixing induction: fan-out < degree') counted dead gates only; the GE above counts the whole trivial simplification.

## 5. Outcome on the 46k corpus (qg-d2, board qg-d2-elim.md, 13:58): GE is 951 in disguise
- GE holds on 46,097 / 46,097 circuits, and the F2 step never holds without GE.
- But by the identity elim1(v) − cost(v) = (s − base) − (s1(v) − base({v})), GE ⟺ ∃ v: slack(C_v) ≤ slack(C), where slack = s − base.
- On the 2,112 tight circuits (s ≤ base + 3), best = s − base EXACTLY. So the best restriction is TIGHT: s1(v) = base({v}), slack 0. (Not "keeps the slack": it removes all of it.) In total, min_v slack(C_v) ≤ slack(C) on 46,029; the 68 exceptions have restrictions with more slack than C.
- So on the corpus GE ⟺ slack(C) ≥ 0 ⟺ 951 for C itself; the data give no independent evidence for GE at a MinCE. Slack monotonicity ("some x_v := 1 does not increase s − base") is the exact content of the elimination step, and it is FALSE for 68 correct circuits.
- Conclusion for (b): what gates < base buys is exactly lex-minimality on subfamilies (`MinCE.sub_bound`, `elim_lt`). Every closing step at the top (elimination, or F2 via |F2| ≤ s) is 951-strength there. A route needs an intermediate quantity that can exceed s − base under restriction (the F2 count can: on MATCH-C |F2(∅)| − base = 15 < s − base = 32, yet the F2 count holds at every cube).
