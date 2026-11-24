Feeds part 2 ("the step") of INDEX.md. (fable-f2-nonlocal lane, 2026-11-24)

# The F2 STEP at NON-LOCAL cubes: FALSE, also under R+, also for F4 / F5

**Verdict.** Target T ("for every correct one-NOT circuit with R1-R4 and an essential NOT, at every cube Q with
base(Q) > 0 where the NOT input h depends on ≥ 2 inputs, GainF2 holds at some v ∉ Q") is FALSE.
Witness MATCH-C (k = 7): n = 16, 55 gates, base 23, h = OR of 14 inputs, R1, R2, R3, R4, R5' and R+ ALL TRUE;
at Q = ∅ every one of the 16 points has gain < cost, for each of the families F1, F2, F4, F5.
The COUNT |F(Q)| ≥ base(Q) holds at all 59,706 cubes with positive base for all four families. Not a 951 counterexample
(55 gates > base 23). The U-game on the lifted outputs of MATCH-C is WON (k = 3, 5, 7; ugame.py), so Theorem G of
fable-global-price.md gives the lifted count there: the witness is inside the proved region of part 3 and outside part 2.

Words: PROVED = paper proof below; CHECKED = computed by two independent programs; TESTED = computed, with counts.

## 1. MATCH-C(k)
Points: A = {u_0..u_{k-1}, y}, B = {a_0..a_{k-1}, y'} (file: u_i = i, y = k, a_i = k+1+i, y' = 2k+1).
Sets: A, B, P_i = {u_i, a_i} (i < k), E = {y, a_0}, E' = {y', u_0}. Pairwise intersections ≤ 1. base = 3k + 2.
Gates (7k + 6; 5k + 3 OR gates):
  j_i = x_y ∧ x_{a_i},  p_i = x_{u_i} ∨ j_i,  f_A = balanced OR tree of p_0..p_{k-1} (pair neighbours, carry the odd one);
  j'_i = x_{y'} ∧ x_{u_i},  p'_i = x_{a_i} ∨ j'_i,  f_B = the same tree of the p'_i;
  h = f_A ∨ f_B,  N = NOT h,  X_A = x_y ∨ x_{a_0},  X_B = x_{y'} ∨ x_{u_0},
  o_A = (X_A ∧ N) ∨ f_A,  o_B = (X_B ∧ N) ∨ f_B,  e_i = p_i ∨ p'_i.
Outputs: o_A, o_B, e_i (for P_i), X_A (for E), X_B (for E').
Functions. Put U = OR x_{u_i}, V = OR x_{a_i}. f_A = U ∨ x_y V, f_B = V ∨ x_{y'} U, h = U ∨ V (depends on 2k inputs).
**Correct (PROVED).** h = 0: U = V = 0, x_{a_0} = 0, so o_A = x_y = OR(A). h = 1: o_A = f_A; if U = 1 it is 1 = OR(A); if U = 0
then V = 1 and f_A = x_y = OR(A). o_B by symmetry. e_i = x_{u_i} ∨ x_{a_i} since j_i ≤ x_{a_i}, j'_i ≤ x_{u_i}. ∎
MATCH-S(k) is the same circuit with e_i = x_{u_i} ∨ x_{a_i} read from the inputs (then p_i is not in the cone of e_i).

**Theorem 1 (PROVED, every k).** In MATCH-C(k) at Q = ∅, for F = F2 and for F = F5:
  gain(u_j), gain(a_j) ≤ depth(j) + 4 + [j = 0] ≤ ⌈log2 k⌉ + 4 + [j = 0],   cost = k + 1 + [j = 0];
  gain(y), gain(y') ≤ 2,   cost = k + 1.
So the STEP fails at Q = ∅ for every k ≥ 7 (k = 7: 7 < 8, 8 < 9, 2 < 8). For MATCH-S the same holds for F2.
*Proof.* The real functions of all wires below h are monotone and as listed. gain_F(v) ≤ number of OR gates not in F({v}), and
F5 ⊆ F2, so it is enough to give, for every OR gate g outside a short list, a witness (alive set w not through v, zero point
Z ∋ v with Z ∩ S_w = ∅, g(Z) = 0, two atoms of S_w with g = 1) with g in the cone of the output of w. Cones: p_i, p'_i are in
cone(e_i); every gate of the f_A tree is in cone(o_B) through h and N, and every gate of the f_B tree is in cone(o_A).
A tree gate of f_A is g_I = OR_{i ∈ I} p_i with |I| ≥ 2; likewise g'_I in f_B.
Case v = u_j (v = a_j is the mirror image).
 - p_i, i ≠ j: set P_i, Z = {y, u_j}: p_i(Z) = 0; + u_i gives 1; + a_i gives 1 (the term x_y x_{a_i}).
 - g_I with j ∉ I: set B, Z = {y, u_j}: g_I(Z) = 0; + a_i gives 1 for each i ∈ I.
 - p'_i, i ≠ j: set P_i, Z = {y', u_j}: 0; + a_i: 1; + u_i: 1.   p'_j: set B, Z = {u_j}: 0; + a_j: 1; + y': 1.
 - g'_I: set B, Z = {u_j}: 0 (every junk term needs x_{y'}); + a_i: 1 for i ∈ I.   o_B: set B, Z = {u_j}.
 - X_A: its own set E, Z = {u_j}.   X_B, if j ≠ 0: its own set E', Z = {u_j}.   e_i, i ≠ j: set P_i, Z = {u_j}.
 Left over: p_j, the g_I with j ∈ I (depth(j) gates), h, o_A, e_j, and X_B when j = 0.
Case v = y (v = y' is the mirror image). Alive: B, all P_i, E'.
 - p_i: set P_i, Z = {y}: 0; + u_i: 1; + a_i: 1.   g_I and h: set B, Z = {y}: 0; atoms a_i (h ∈ cone(o_B)).
 - p'_i: set P_i, Z = {y, y'}: 0; + a_i: 1; + u_i: 1.   g'_I, o_B: set B, Z = {y}.   X_B: set E', Z = {y}.   e_i: set P_i, Z = {y}.
 Left over: o_A and X_A.
Costs: u_j lies on A (k) and P_j (1), and u_0 also on E' (1); y lies on A (k) and E (1). ∎
(Computed gains equal these bounds for k = 7, 8; all 5k + 3 OR gates are in F2(∅).)

**CHECKED for k = 7 (file 951/data/witnesses/nonlocal/match_c_k7.json).**
- F2 at Q = ∅ by three programs with no shared code: f2lib bit tables (f2_nonlocal_build.py), numpy (f2_nonlocal_check.py),
  brute force from the definition (f2_cex_check.py): gains 8,7,7,7,7,7,6,2 | 8,7,7,7,7,7,6,2 against costs 9,8,8,8,8,8,8,8 twice.
- F1, F4, F5 at Q = ∅ by two programs (numpy; the `build` of family_table.py through f2_nonlocal_fam.py): best gain − cost = −1.
- All cubes (numpy): 59,706 cubes with positive base; count fails at 0 for F1, F2, F4, F5 (minimum slack 0); the step fails at
  exactly 1 cube, Q = ∅, which is non-local. Only Q ⊆ {y, y'} are non-local (4 cubes); elsewhere h ≡ 1 on the cube.
- R1 (no constant gate), R2, R3, R4, R5' (C_0 and C_1 both wrong), and R+ for EVERY wire including the inputs, every nonempty
  set of its readers, both constants: 0 violations (f2_rplus_all.py). Same for k = 8 (n = 18, 62 gates, base 26; step fails by 2).
- Local closures of CubeF2.lean at Q = ∅: not CubeLocal (h depends on 14 inputs). LW1 fails (by hand): h(z) = 0 forces
  z ⊆ {y, y'}, so |B \ z_A| ≥ k and |A \ z_B| ≥ k. So the hypothesis H of `no_minCE_of_gainF2_or_local` is false for MATCH-C
  as a correct circuit; H is only asked of a MinCE, and MATCH-C is not one.

**Why R+ holds here and not in TWIN-TREE.** h = U ∨ V is 1 at every matched point, so the direct path x_y ∧ N is switched off
exactly where a junk term x_y x_{a_i} is needed: every junk term is essential. The leak that makes C_1 wrong (X_A = x_y ∨ x_{a_0})
is itself the output gate of the extra set E, so it cannot be cut. Size of the failure: the gates above a junk leaf leave only
under their own singles (⌈log2 k⌉ of them), cost is linear in k.

## 2. Small variants (n = 14, TWIN-TREE-N with a non-local h; R+ false as in TWIN-TREE-N)
951/data/witnesses/nonlocal/twin_tree_{or2,e0,and2,maj3}.json: h = x0 ∨ x8; h = x1 ∨ x8 (the output gate of P_0, read by both
big outputs, both inputs of h needed); h = x8 ∧ x10; h = MAJ(x8, x10, x12). In each the NOT is essential, R1-R4 hold, the old
gates keep their real functions and the new OR gates have no witness, so Theorem 1 of fable-f2-step.md applies verbatim:
F2 and F1 STEP fail at Q = ∅ (CHECKED, numpy + bit tables). F4 / F5 STEP hold on these four (best gain − cost = +3) and on
MATCH-S (+5); F4 / F5 die only on MATCH-C.

## 3. What survives (weakest surviving hypothesis)
- Dead as statements about correct circuits, even with R1, R2, R3, R4, R5', R+ and h non-local: the x_v := 1 STEP for F1, F2,
  F4, F5 and every rule for choosing v. These R-facts are all the local consequences of MinCE in MinCERed.lean
  (no_const, no_dup, no_var, live, not_used, observable). So a proof of GainF2 at non-local cubes for a MinCE must use
  `gates.length < base` (or `MinCE.false_of_shorter` for a circuit that is not a constant substitution) in the argument itself.
  With s < base the step is not weaker than 951: MATCH-C has |F2(∅)| − base = 2k + 1 spare gates, and the step fails by 1.
- Alive: the COUNT at every cube (0 failures here), i.e. the first disjunct of `base_le_F2_pts_or`. On MATCH-C it follows from
  the lifted Theorem U (U-game won). So non-local cubes should be closed by a direct count (part 3), not by a point step.
- TESTED only, one cube: the deletion step x_v := 0 at Q = D = ∅ (gain0 ≥ number of sets through v) HOLDS on MATCH-C k = 7
  (e.g. v = u_1: 3 ≥ 2; v = y: 8 ≥ 2) and on twin_tree_e0. A mixed induction (x_v := 1 or x_v := 0) is not refuted by these
  witnesses; for UC it is dead on PAPPUS-JUNK (DEAD_ENDS.md), for F2 it is untested beyond this line.
- Not attempted: T at the U-game obstruction ({0,1,2}, {0,3,4}, h = x1 ∨ x3). T is false in general, so a hand proof there
  would be a statement about one instance only.

## 4. TESTED (corpora in the repo, restricted to non-local cubes)
`f2_nonlocal_suite.py . 14`: 109 correct one-NOT circuits with n ≤ 14 (every JSON in the repo, including the four n = 14
variants of §2), 108,235 cubes with positive base, 31,078 of them non-local. F2 STEP fails at a non-local cube on exactly the
4 new variants (Q = ∅ each); F1 also on pappus_junk_gain (known); F4, F5: 0 failures; count: 0 failures for all four.
Without the new files: the 105 old repo circuits have 0 F2 STEP failures at their 14,270 non-local cubes (their only F2 failures are the two
twin trees at Q = ∅, local). The barrier suite alone (`951/data/witnesses 14`): 19 circuits, 57,550 cubes, 16,985 non-local.
The n = 16 witnesses are in the subdirectory `nonlocal/` so that family_table.py (which globs data/witnesses/*.json and
loops over 2^n cubes in pure Python) keeps its running time and its 19,534 count.

## 5. Commands (repository root; python with -I; numpy needed for *_check and *_suite)
- `python3 -I 951/tools/kill_tests/f2_nonlocal_build.py [outdir]`   builds all variants, F2 step at Q = ∅ (MATCH: k = 3..8).
- `python3 -I 951/tools/kill_tests/f2_nonlocal_check.py FILE.json`  F1/F2/F4/F5 count and step at every cube, with locality.
- `python3 -I 951/tools/kill_tests/f2_nonlocal_fam.py FILE.json`    second method (family_table.py definitions) at Q = ∅.
- `python3 -I 951/tools/kill_tests/f2_cex_check.py FILE.json`       third method for F2 (about 1 min at n = 16).
- `python3 -I 951/tools/kill_tests/f2_rplus_all.py FILE.json`       R1-R5' and R+ on all wires.
- `python3 -I 951/tools/kill_tests/f2_nonlocal_suite.py ROOT NMAX`  corpus run.
