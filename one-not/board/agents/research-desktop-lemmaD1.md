> **OFF THE ROUTE (main, 2026-11-24 14:45): lemma candidate D1 is refuted (this note says so); row in one-not/DEAD_ENDS.md. Kept for the record; do not build on it.**

# research-desktop: lemma candidate D1 (D at every I1 point) — REFUTED; why D's argument cannot extend; corrected candidates

Kill test: `research-desktop-lemmaD1-killtest.md` (REFUTED, witness n = 4). This file: the analysis.
(Coordinator redirect: stop proving D1; record the refutation, pinpoint the broken step, propose a corrected candidate.)

## 1. Statement (Lean names; `one-not/lean/PEqualNP/W951/CanonD1.lean`, see §6)

Lift `C = lift n p gates` on n+1 inputs (y = last input). `K1Z gates p R Z` = OR gates of C with `C(g)(Z,1) = 0` and
`C(g)(e_u,1) = 1` for >= 2 u ∈ R (`K1Z … (Zof R) = K1`). `K0of gates p R' m` = OR gates with `C(g)(top_v,0) = 0` and
`C(g)(m_{u'} + e_{u'}, 0) = 1` for >= 2 u' ∈ R' (per-atom bases; constant m gives `K0`).
**D1**: correct one-NOT circuit, |S_w ∩ S_v| <= 1, Z an I1 point of w (Z ∩ S_w = ∅, h(Z) = 0, maximal), m an I0 choice of v
(m_{u'} ∈ Min(h), m_{u'} ∩ S_v ⊆ {u'}) with every m_{u'} ∩ S_w = ∅ ⇒ K_1(w; Z) ∩ K_0(v; m) = ∅ (classes, hence merge sets).

## 2. Refutation (kill test witness, re-checked)

n = 4, sets {01},{02},{03},{12},{13}, h = x1 ∨ x3, w = {0,1}, v = {0,2}, Z = {2} (top_w = {2,3}, T = {3}), m = ({3},{3}).
Shared merge gate wire 10 = x0 ∨ w7, w7 = h ∧ (x2 ∨ y): world 1: w7 = x1 ∨ x3; world 0: w7 = (x1 ∨ x3) ∧ x2.
At (Z,1) = ({2},1): x0 = 0, w7 = 0. At e_0: x0 = 1; at e_1: w7 = 1 → merge of 0,1. At (top_v,0) = ({1,3},0): x0 = 0, w7 = 0
(x2 = 0). At ({0,3},0): x0 = 1; at ({2,3},0): w7 = 1 → merge of 0,2. Collision. (Note: this circuit has 11 gates for five
2-sets, monotone optimum 5: it is far from minimal.) Caution: d1.py writes `witnesses_shard*.json` into its own folder and
then also loads them as corpus (they are .json under the root one-not/); the current shard files were overwritten by a later
run (circuit names `…witnesses_shard0.json:2`); content is the same witness.

## 3. The exact step where D breaks for Z ≠ top_w

D (`disjoint_K0_K1`) = `orClz_disjoint`: a gate in both classes is 0 at the second zero point and 1 at two atoms of the first
system, so it suffices that of any two atoms one lies BELOW the other zero point. With first system the world-0 atoms
`(m_{u'} ∪ {u'}, 0)` and second zero point `(Z, 1)`:

  (m_{u'} ∪ {u'}, 0) <= (Z, 1)  ⇔  m_{u'} ∪ {u'} ⊆ Z.

At Z = top_w this is `(m_{u'} ∪ {u'}) ∩ S_w = ∅`, true for all u' but the (at most one) point of S_v ∩ S_w. **For an I1
point it fails for EVERY u'**: m_{u'} is a minterm of h (h(m_{u'}) = 1) and h(Z) = 0, so m_{u'} ⊄ Z by monotonicity of h.
(Equivalently: m_{u'} avoids S_w, so m_{u'} ∈ Min_w, and the transversal T = top_w \ Z meets it. In the witness
m = {3} = T.) The other orientation is never available: a world-1 atom has y = 1 and is not below any (Z', 0). And the
world-1 atoms e_u (u ∉ Z) are not below (Z,1)-irrelevant. So after Z ≠ top_w NO monotonicity comparison is left between
the two systems: the four constraints (0 at (Z,1), 0 at (top_v,0), 1 at two e_u with y=1, 1 at two m+e_{u'} with y=0) are
jointly satisfiable by one OR gate. Lean: `atom0_not_le_Z`, `atom1_not_le_ext_false`, `D_hyp_fails`.

Side remark: D at Z = top_w with avoiding minterms is itself vacuous in the I1 setting: top_w is an I1 point only for type B
(h(top_w) = 0, Min_w = ∅), and then no minterm avoids S_w. So D1 is not an "extension" of a used case; the typeA count
"Z = top_w & all avoiding" has 0 pairs for that reason.

## 4. Corrected candidates and tests

**(a) D1' := D1 + Z ∩ S_v = ∅ (Z <= top_v).** Kills the witness (Z = {2} meets S_v = {0,2}; same for the second witness).
Full kill test (copy of d1.py with the extra split, roots one-not/ + /home/user/corpora, 31,587 circuits): all 4 collisions have
Z ∩ S_v ≠ ∅; **0 collisions in 33,632 tuples with Z ∩ S_v = ∅.** BUT D1' is FALSE for correct circuits in general
(merge sets too): n = 5, S_w = {0,1}, S_v = {2,3}, h = x2 ∨ x3 ∨ x4, Z = ∅ (T = {2,3,4}), m = ({4},{4}):

    a = x2 ∨ x4; hh = a ∨ x3; y = ¬hh; P = (y ∧ x0) ∨ x2; Q = (y ∧ x1) ∨ x3; g = P ∨ Q; outputs x0 ∨ x1, x2 ∨ x3.

g is a merge in K_1(w; ∅) (P = 1 only at e_0, Q only at e_1, both 0 at (∅,1)) and in K_0(v; m) (y = 0: P = x2, Q = x3,
0 at top_v = {0,1,4}; P = 1 only at {4,2}, Q only at {4,3}). d1.py on this circuit: 4 collisions, all with Z ∩ S_v = ∅.

**(b) Why no condition on (h, S_w, S_v, Z, m) alone can work.** For ANY instance with |S_w|, |S_v| >= 2, h(Z) = 0: pick
u1 ≠ u2 ∈ S_w, u'1 ≠ u'2 ∈ S_v, A_i = AND of the variables of m_{u'_i} ∪ {u'_i}, and append the junk gates for
g = (y ∧ x_{u1} ∨ A1) ∨ (y ∧ x_{u2} ∨ A2) right after the NOT. A_i is 0 at (Z,1) (m_{u'_i} ⊄ Z since h(Z) = 0) and at
(top_v,0) (u'_i ∉ top_v); 1 at its own world-0 atom; 0 at the other one (u'_i ∉ m_{u'_j} as m_{u'_j} ∩ S_v ⊆ {u'_j}); 0 at
every e_u (that would need m_{u'_i} ⊆ {u} ∩ ... i.e. m_{u'_i} = ∅, h ≡ 1). y ∧ x_u is 0 at Z and in world 0. So
g ∈ K_1(w;Z) ∩ K_0(v;m) (classes; for merge sets the two concrete circuits above suffice), correctness unchanged. Hence
**every true version of D1 must use the circuit (gate budget / every gate needed), not only h, the sets, Z and m.**

**(c) Proposed corrected candidate D1-min**: D1 (or D1') for a minimal counterexample (`MinCE`: fewer gates than Σ_w d_w,
every gate on a path to an output). UNTESTABLE on the current corpus: 0 of the 179,614 tuples come from a circuit with
|G| <= Σ d_w (the corpus has no saving circuit, as 951 predicts). Both junk counterexamples and the witness have
|G| > Σ d_w. A corpus of "every gate needed" circuits (no junk) would at least test the weaker form; the n = 4 witness's
gate 10 does feed output 12, so "every gate needed" alone does not kill it — only the size bound does.

## 5. Consequence for (iii) in research-typeA-menus.md

(iii) does not reduce to the forced-meeting condition of (ii) by a D-type (monotonicity) argument; type A I1 points never
admit one. Whatever excludes (iii) collisions must come from the gate budget.

## 6. Lean (CanonD1.lean; written before the redirect; no sorry)

`disjoint_K0of_K1` (D at top_w with per-atom I0 choices), `disjoint_K0of_K1Z_of_le` (D's argument at any Z, under the
atoms-below-Z hypothesis), `atom0_not_le_Z`, `atom1_not_le_ext_false`, `D_hyp_fails` (§3), `D1Stmt` and `not_D1Stmt`
(D1 refuted on the n = 5 junk circuit x4-version: y = ¬x4, P = y x0 ∨ x4 x2, Q = y x1 ∨ x4 x3, Z = {2,3}, m = {4}).
Build: `lake build PEqualNP.W951.CanonD1` OK, 0 errors; `#print axioms` for all of these: [propext, Classical.choice,
Quot.sound]; no sorry, no native_decide. No Lean for D1' / D1-min (refuted in general / untestable).
