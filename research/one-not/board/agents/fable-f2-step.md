# The F2 STEP (fable-f2-step lane, 2026-11-24)

**Verdict: the F2 STEP is FALSE for correct one-NOT circuits.** It fails at Q = ∅ on TWIN-TREE (n = 14, 28 gates,
base 15, monotone with an unread NOT) and on TWIN-TREE-N (n = 14, 30 gates, the NOT is read and essential; R2, R3, R4,
R5' all hold; only R+ fails, at 5 junk edges). At every one of the 14 points gain(v) < cost(v). So is every statement
that implies the step for all correct circuits: SEE+K3, REROUTE, ABSORB (PROOF_PLAN_SUGGESTIONS §6), the cone
certificate (D) + (S) of qg-d2-ucert.md, LIGHT-STAR, and any rule for choosing v.
The COUNT is not touched: |F2(Q)| ≥ base(Q) holds on both circuits at all 9,504 Q with an alive set (minimum slack 2).
What dies is the induction over points x_v := 1 with F2 as the family, as a statement about all correct circuits.

Words: PROVED (paper proof here), CHECKED (computed), OPEN.

## 0. Statement tested
F2(Q) = OR gates g with a real witness (alive w, Z ⊇ Q, Z ∩ S_w = ∅, u ≠ u' ∈ S_w, g(Z) = 0, g(Z + e_u) = g(Z + e_u') = 1).
gain(v) = |F2(Q) \ F2(Q ∪ {v})|, cost(v) = Σ_{alive w ∋ v} (|S_w| − 1). STEP(Q): some v ∉ Q in an alive set has
gain(v) ≥ cost(v).

## 1. TWIN-TREE (PROVED and CHECKED)
Points 0..13. Sets A = {0,..,6}, B = {7,..,13}, P_i = {2i+1, 2i+8} for i = 0,1,2 (pairwise meeting in ≤ 1 point).
In A: plain leaves t_i = 2i, junk leaves u_i = 2i+1, enabler y = 6; the partner of u_i is a_i = 2i+8 ∈ B.
In B the same with t'_i = 2i+7, u'_i = 2i+8, y' = 13, partner of u'_i is 2i+1 ∈ A. Gates, for X = A (and likewise B):
  j_i = x_y ∧ x_{a_i},  p_i = x_{u_i} ∨ j_i,  m_i = x_{t_i} ∨ p_i  (i = 0,1,2),  c = m_0 ∨ m_1,  f = c ∨ m_2,  o_X = f ∨ x_y,
and e_i = x_{2i+1} ∨ x_{2i+8} (the output of P_i). One NOT gate (of x_0), read by nothing. 28 gates, 21 OR gates.
Correct: every junk term x_y x_{a_i} is ≤ x_y ≤ o_A, so f ∨ x_y = OR(A). File: research/one-not/data/witnesses/twin_tree_f2step.json.

**Theorem 1.** At Q = ∅ every point v has gain(v) < cost(v):
plain leaves t_0, t_1: gain 4, cost 6; t_2: 3, 6; junk leaves u_0, u_1: 6, 7; u_2: 5, 7; enablers y: 1, 6 (same in B).
*Proof.* All wires are monotone. gain(v) ≤ number of OR gates that are NOT in F2({v}); we show every OR gate outside the
following list stays in F2({v}). Let v ∈ A (B is symmetric). Call u a *single* of g if g(e_u) = 1.
(a) Gates of the A-gadget p_i, m_i, c, f of which v is not a single. Such a gate contains a junk term j_i (p_i, m_i: that
i; c: i = 0; f: i = 0) with u_i a single of the gate, hence u_i ≠ v. Witness for the set P_i = {u_i, a_i}:
Z = {y, v} (Z = {y} if v = y). Z ∩ P_i = ∅. g(Z) = 0: the singles of g lie in A \ {y} and v is not one of them, and
every junk term needs some x_{a_k}, a_k ∉ Z. g(Z + e_{u_i}) = 1 (single). g(Z + e_{a_i}) = 1 (the term x_y x_{a_i}). v ∈ Z.
(b) Gates of the B-gadget. p'_i = x_{u'_i} ∨ x_{y'} x_{u_i}: witness for B with Z = {u_i, v}, atoms u'_i, y'
(Z ∩ B = ∅; p'_i(Z) = 0; p'_i(Z + e_{y'}) = 1 by the junk term). m'_i, c', f', o_B: witness for B with Z = {v} and two
singles in B (the gate is 0 at {v}: v ∈ A occurs in the B-gadget only inside terms x_{y'} x_u).
(c) e_i with v ∉ P_i: witness for P_i with Z = {v}.
So the only gates that can leave are: the A-gadget gates with single v, o_A, and e_i if v ∈ P_i. Singles: t_i is a
single of m_i, f, and of c if i ≤ 1; u_i of the same gates and of p_i; y of nothing. Counting with o_A (and e_i for u_i)
gives the list. cost(t_i) = cost(y) = 6, cost(u_i) = 6 + 1. ∎
(The computed gains equal these upper bounds, so all 21 OR gates are in F2(∅): |F2(∅)| = 21 ≥ 15.)

**TWIN-TREE-N (the NOT is read).** Replace o_A = f ∨ x_6 by X = x_6 ∨ x_8, h = x_8, N = NOT x_8, o_A = (X ∧ N) ∨ f.
Correct: where x_8 = 0, X ∧ N = x_6 and x_6 ∨ f = OR(A); where x_8 = 1, the junk term x_6 x_8 of f gives f = OR(A).
C_1 (N := 1) computes x_6 ∨ x_8 ∨ f ≠ OR(A); C_0 computes f ≠ OR(A). The real functions of all old gates are unchanged;
X has no witness (its only possible atoms are 6 and 8, on no common set); the new output gate has the real function
OR(A). So Theorem 1 holds verbatim. File: research/one-not/data/witnesses/twin_tree_N_f2step.json (30 gates). Here h is a single
variable, the case in which the COUNT is proved (front A2, NotVarF2): the count holds, the step does not.

**Mechanism (why random search missed it).** A junk term x_y ∧ x_a with y ∈ S_w, attached at a leaf u of the OR tree of
S_w, where {u, a} lies on another set not through y: every tree gate above the leaf becomes, after x_v := 1 for any v
that is not one of its singles, a real merge for that other set, so it leaves only under its own singles. A gate of a
balanced tree has few singles. For a set of size m with one junk leaf per bottom pair, a point collects about
log2(m) + 3 leaving gates against cost m − 1; the attaching gate p costs one extra F2 gate with one single. A set of
size 3 is exactly tight (per-set total 6 = 2·3), size 4 with a chain loses 1 (11 < 12), size 7 balanced loses at every
point. Two such sets serve each other through the pairs P_i, so no point is left to pay. k = 1, 2 (sets of size 3, 5):
the step holds; k = 3, 4: fails (f2_cex_build.py).

## 2. What the witnesses do NOT satisfy, and what stays OPEN
- R+ fails: TWIN-TREE-N has exactly 5 removable edges (f2_rplus.py): the junk gates x_6 ∧ x_10, x_6 ∧ x_12, x_13 ∧ x_1,
  x_13 ∧ x_3, x_13 ∧ x_5 can be replaced by 0. (x_6 ∧ x_8 is essential there.) R2, R3, R4, R5' hold (f2_cex_check.py).
- **OPEN: STEP for a circuit satisfying R+.** No circuit with R+ is in any corpus, so this cannot be tested. I could
  not make all junk essential with one NOT: a junk term x_y x_a is essential only if h(e_a) = 1 and the direct path
  for x_y is switched off by N there, and wrongness of C_1 that keeps the wires of h essential must enter through an
  OR gate reading inputs directly; with one NOT this made O(1) junk terms essential in every variant I tried (not a
  proof). Note also that R+ at the fixed circuit says nothing about the restricted circuit on a cube Q ≠ ∅, where the
  induction needs the step: a term x_y x_a x_q that is essential in the circuit is plain junk on the cube x_q = 1.
  So even under R+ the step at ALL Q is in doubt; the smallest obstruction to look for is an R+ circuit whose
  restriction to some cube is TWIN-TREE.
- Not refuted: the count |F2(Q)| ≥ base(Q) (MU for F2); the lifted / price forms; anything that uses s < base.

## 3. PROVED on the positive side (small)
**Lemma K (cube where h is constant).** Let h be constant on {Z ⊇ Q}. For alive w put
K(w) = {OR gates g : g(top_w) = 0 and g(Q + e_u) = 1 for at least two u ∈ S_w} (real values). Then |K(w)| ≥ |S_w| − 1,
the K(w) are pairwise disjoint, and every g ∈ K(w) leaves F2 under x_v := 1 for every v ∈ S_w with g(Q + e_v) = 1.
Hence gain(v) ≥ Σ_{alive w ∋ v} #{g ∈ K(w) : g(Q + e_v) = 1} ≥ number of alive sets through v, and if every alive set
through v has size 2 then gain(v) ≥ cost(v) (in such a cube EVERY point of a graph system is good).
*Proof.* On the cube the real circuit is the monotone circuit C_c (c the constant value of NOT). Size: GM
(PROOF_PLAN_SUGGESTIONS §2) in C_c with zero point top_w and atoms Q + e_u; condition (2) holds since the variables
outside top_w are those of S_w. Members are in F2(Q): g(Q) ≤ g(top_w) = 0, witness at Z = Q. Disjoint: g ∈ K(w) ∩ K(w'),
w ≠ w': some u ∈ S_w \ S_w' has g(Q + e_u) = 1 and Q + e_u ⊆ top_w', against g(top_w') = 0. Leaving: g(Q + e_v) = 1 and
monotone give g ≡ 1 above Q + e_v, so no zero point. Count: in the union-find run the first merge involving v's block
has v in its block. ∎  (TWIN-TREE shows the bound cannot be raised to cost(v) for larger sets.)

Also checked while reading the other notes: F1* (dwV8p-synth-F1-F2.md §1) is correct as written (the proof is three
lines of monotonicity); the joint union-find count (§6 Step 2) is correct (the NOT gate has an empty block whenever it
is 0 at Q). Both are true and both are useless for an all-circuits step, because the step is false.

## 4. TESTED only (before the counterexample; kept for the record)
- Rule "v maximises t(v) = #{g ∈ F2(Q) : g(Q) = 0, g(Q + e_v) = 1}": every argmax is good on 197,912 instances
  (9,076 circuits: repo corpus n ≤ 9 + JUNK2 + light_gen seeds 1-3 × 3000), `f2x_rules2.py 1 4`. On TWIN-TREE the
  argmax (u_0) is bad like every other point. JUNK2 and ess_rand_clean_744: the rule picks a good point (v = 2, v = 1).
- 'least h-influence, ties by index' fails for F2 on JUNK2 (v = 0: gain 1 < cost 2), as it did for UC.
- Matching form (each alive w through v gets |S_w| − 1 leaving gates that have a w-witness, all distinct): some v on
  197,912 / 197,912 (`f2x_match.py 1 4`).
- The plan's single-zero-point form (each w through v has ONE zero point Z_w with M_{Z_w}(w) ⊆ leaving gates, pairwise
  disjoint): per set, some v on 23,406 / 23,406; with disjointness FAILS on 3 (first: cx44_1_junk.json, Q = ∅)
  (`f2x_single.py 1 2`, n ≤ 7).
- Local search for a failure (`f2_adv.py`, redirect / flip / insert moves from random starts) reached only gain = cost.
  The counterexample came from the per-set calculus of §1, not from search.

## 5. Commands (from the repository root)
- `python3 -I research/one-not/tools/kill_tests/f2_cex_build.py [A.json B.json]`  builds k = 1..4 and TWIN-TREE-N, bit-table harness.
- `python3 -I research/one-not/tools/kill_tests/f2_cex_check.py research/one-not/data/witnesses/twin_tree_f2step.json`  independent brute force
  from the definition (no shared code); also prints R2, R3, R4, R5'. Same for twin_tree_N_f2step.json. About 2 min each.
- `python3 -I research/one-not/tools/kill_tests/f2_allQ.py FILE.json`  count and step at every Q: step fails at exactly 1 of 9,504 Q
  (Q = ∅), count at none.
- `python3 -I research/one-not/tools/kill_tests/f2_rplus.py FILE.json`  R+ violations.
- Library `f2lib.py` (tables, F2, gain, cost, Lemma M runs, corpus, random generator).
