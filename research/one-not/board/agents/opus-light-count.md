> **OFF THE ROUTE (main, 2026-11-24 14:45): LIGHT-COUNT over UC is false for general circuits (PAPPUS-JUNK); row in research/one-not/DEAD_ENDS.md. Kept for the record; do not build on it.**

# LIGHT-COUNT (opus lane, 2026-11-24)

**Verdict: LIGHT-COUNT is FALSE.** So is the hypothesis of `muc_of_gainOne_pts` / `base_le_UC_one`
(`proofs/w951/PEqualNP/W951/MUInduct.lean`), and so is the hypothesis of the combined induction `base_le_UC`
(x_v := 1 or x_v := 0 at some point). The witness is a correct one-NOT circuit, light at the ROOT
(D = Q = ∅), so no rule for choosing v and no order of moves can rescue the point induction for this UC.
MU itself (|UC| ≥ base) still holds on it (20 ≥ 18): what dies is the induction, not the count.

Witness: `research/one-not/data/witnesses/pappus_junk_gain.json` (PAPPUS-JUNK, n = 9, 66 gates, base 18).
Check: `python3 -I research/one-not/tools/kill_tests/light_cex.py research/one-not/data/witnesses/pappus_junk_gain.json`
(an independent brute-force evaluator written straight from the definition, 0.2 s). The bit-table
harness of `mu_light.py` gives the same numbers.

## 1. Definitions (as in `fable-mu-induction.md` §0 and `MUInduct.lean`)

h = input of the NOT gate, C_0 / C_1 = the circuit with NOT := 0 / 1. UC(D,Q) = OR gates g with a witness
(alive w, a ≠ b ∈ S_w − D, Z ⊇ Q, Z ∩ (D ∪ S_w) = ∅) of face 1 (h(Z) = 0, C_1(g)(Z) = 0,
C_1(g)(Z+a) = C_1(g)(Z+b) = 1) or face 0 (h(Z+a) = h(Z+b) = 1, C_0(g)(Z) = 0, C_0(g)(Z+a) = C_0(g)(Z+b) = 1).
Gain of x_v := 1 is |UC(D,Q) − UC(D,Q+v)|, cost Σ_{alive w ∋ v} (|S_w − D| − 1).

## 2. PROVED

**Lemma D (exact death criterion).** g ∈ UC(D,Q) leaves under x_v := 1 iff no witness of g at (D,Q) has
v ∈ Z. *Proof.* A witness at (D, Q+v) is a witness at (D,Q) with v ∈ Z (and then v ∉ S_w, so w stays
alive). Conversely a witness at (D,Q) with v ∈ Z has Z ⊇ Q + v and S_w ∌ v, so it is a witness at (D,Q+v). ∎
So gain(v) = #{g ∈ UC : v ∉ Zall(g)}, Zall(g) = union of the zero points of the witnesses of g.

**Lemma R (real witnesses are UC witnesses).** If real g(Z) = 0 and real g(Z+a) = real g(Z+b) = 1 with
a ≠ b ∈ S_w − D, Z ⊇ Q, Z ∩ (D ∪ S_w) = ∅, then g has a UC witness at Z.
*Proof.* If h(Z) = 0: C_1 = real on {h = 0}, so C_1(g)(Z) = 0, and C_1 ≥ real gives the atoms (face 1).
If h(Z) = 1: h is monotone so h(Z+a) = h(Z+b) = 1, and C_0 = real on {h = 1} (face 0). ∎
(Used to build witnesses quickly; it also shows a "junk" gate that becomes a real merge after a move is
always still counted, which is the mechanism of every bad point found.)

**Theorem (LIGHT-COUNT is false).** Let P = Z_3², columns K_x = {(x,y)}, sets = the 9 non-vertical lines
(slope m, intercept b) of AG(2,3) (the Pappus configuration: two points lie on a common set iff they are in
different columns, and then on exactly one). For each line w let r_w be its point in column m (slope m);
this is a bijection lines → points. Let p_w, q_w be its other two points (either order) and {c_w, d_w} =
K(q_w) − q_w. Circuit:
* column gates, for each column {a,b,c}: s = x_a ∨ x_b, s' = s ∧ x_c, M = (x_a ∧ x_b) ∨ s' (= "≥ 2 ones in
  the column"); T = M_0 ∨ M_1, H = T ∨ M_2; h = H, N = NOT H;
* per line w: A_w = (x_c ∧ x_d) ∧ x_r, J_w = A_w ∧ N, t_w = x_q ∨ J_w, g_w = x_p ∨ t_w, o_w = g_w ∨ x_r.

Correct: real J_w ≡ 0 because x_c x_d ≤ h, so o_w = x_p ∨ x_q ∨ x_r. Exactly one NOT. At D = Q = ∅ the
instance is light: h(∅) = h(e_x) = 0, h ≢ 0, every point lies on 3 alive sets (no free point). Claim: at
every v, gain of x_v := 1 is 5 and cost is 6.

*Proof.* Faces: C_0(J_w) = 0, C_1(J_w) = x_c x_d x_r; the column gates, T, H do not depend on N.
The OR gates are the 3 gates s, the 3 gates M, T, H, and t_w, g_w, o_w.
(i) s and M depend only on the variables of one column; two atoms of a witness would lie in one column,
and no set contains two points of a column. Not in UC.
(ii) t_w ∉ UC. Face 0: C_0(t_w) = x_q has one atom. Face 1: C_1(t_w) = x_q ∨ x_c x_d x_r; atom r needs
c, d ∈ Z, but then h(Z) = 1; atom c needs r, d ∈ Z and gives only the pair {q, c}, atom d only {q, d},
both inside a column; c and d are never atoms together.
(iii) g_w, o_w ∈ UC: face 1 at Z = ∅ with atoms p, q (h(∅) = 0, J needs three ones).
(iv) T and H are in UC and never leave: for any v, take Z = one point from each of two columns, chosen to
contain v, the two columns being those of v and one other (for v in column 2 and gate T, take
Z = {v, x_0, x_1}); h(Z) = 0, real T(Z) = 0, and the two atoms a, b are column-mates of the two chosen
points in columns 0, 1, chosen so that the line through a, b misses Z (of the 4 choices of (a,b) at most 2
lines pass through a given third point); Lemma R gives the witness, with v ∈ Z.
(v) Fix v. It is r of exactly one line w_0 and p or q of the other two lines w_1, w_2 through it.
o_{w0}, o_{w1}, o_{w2} and g_{w1}, g_{w2} have C_0 ≥ x_v, so they leave (Lemma C0, `not_UCWit_of_C0`):
5 gates. g_{w0} stays: Z = {r, d} with r = v, face 1: h(Z) = 0 (r and d lie in different columns, since
d is in q's column and q, r are on one line); C_1(g)(Z) = 0; C_1(g)(Z+p) = 1; C_1(g)(Z+c) = 1 via
x_c x_d x_r. p and c lie in different columns, so on one line w''; w'' ∌ r (w'' ∩ w_0 = {p}) and
w'' ∌ d (d is c's column-mate), so Z avoids w'' and w'' ∌ v. g_{w'}, o_{w'} for w' ∌ v stay: Z = {v},
face 1, atoms p_{w'}, q_{w'}. By (i), (ii), (iv) nothing else is in UC. Gain 5, cost 3 · 2 = 6. ∎

For the orientation of p/q stored in the witness file, x_v := 0 also fails at every v (gains
2,2,1,0,2,0,1,0,1 against deg 3; computer check, two independent implementations), so the combined
hypothesis of `base_le_UC` fails at (∅, ∅) too. (With the other orientation, x_v := 0 is good at v = 3:
the x := 1 part above is orientation-free.)

Mechanism. g_w survives x_r := 1 through a face-1 witness whose ATOM Z + c = {r, c, d} lies in
{h = 1}, where C_1 ≠ real (real J_w = 0, C_1(J_w) = 1). The face-1 definition asks h = 0 only at Z. Every
such witness costs nothing in the real circuit, so the gain bound cannot hold for this UC.

## 3. TESTED (and refuted candidate rules)

* `light_probe.py` (helper: light instances of the corpus, same sampling as `mu_light.py`).
* `light_gen.py one-not SEED COUNT`: random correct one-NOT circuits with junk (pool of AND/OR gates, one
  NOT, outputs = OR trees over the atoms plus random wires ≤ o_w), D = ∅, all Q.
  Seeds 1-4 × 5,000 circuits: some v good on every light instance (12,970 + 12,671 + 12,292 + 12,996),
  every heavy and h-const instance too. Random junk does not find PAPPUS-JUNK: the counterexample needs a
  configuration where every point is the r of a line and every q has two column-mates off all sets.
* Rule "least h-influence, ties by index" (fable's candidate): refuted by JUNK2 (n = 6, sets {0,1,2},
  {2,3}, {4,5}; gates 6 = x0∧x3, 7 = x4∧x5 = h, 8 = NOT 7 (unused), 9 = x2∨6, 10 = x1∨9, 11 = 10∨x0,
  12 = x2∨x3, 13 = x4∨x5): light at ∅, v = 0 has influence 0 and index 0, gain 1 < cost 2.
* Uniform averaging AVG (Σ_v gain ≥ Σ_v cost over alive v, which would give LIGHT-COUNT with no rule):
  held on all 3,891 corpus light instances and all random ones, failed on 9 corpus HEAVY instances, and
  fails on PAPPUS-JUNK (45 < 54). Per-set averaging (over S_w, every w): fails on random light circuits
  (gen1_4342, gen3_2853, gen3_4988).
* Repair "face 1 also asks h(Z+a) = h(Z+b) = 0" (kills the mechanism above): breaks MU itself
  (hard4.json:0, Q = {1}: |UC| = 1 < base 2). Dead.

## 4. OPEN / what remains

Nothing remains of LIGHT-COUNT as stated: it is false at the root of a light instance, for UC exactly as
in `MUInduct.lean`. Smallest obstruction found: PAPPUS-JUNK (n = 9, Q = D = ∅, every v; for v = r_w the
surviving gate is g_w with witness Z = {r_w, d_w}, atoms p_w, c_w). A repair has to change the counted
family so that face-1 witnesses whose atoms leave {h = 0} through a NOT-dependent AND term (J_w) are not
counted, without losing MU (the plain strict version loses it on hard4). Whether some other family keeps
both MU and a gain lemma is for coord to decide; on this circuit UC − {T, H} has exactly base = 18 gates,
so any family must keep essentially all of g_w, o_w.
