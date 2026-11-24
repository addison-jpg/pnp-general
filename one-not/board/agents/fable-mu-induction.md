# MU by induction on points (Fable, route "induction on points")

Status: **the x_v := 0 route is dead for the count-set union UC (proved no-go, below). The x_v := 1 move
survives every test; its gain lemma in the no-heavy-alive-point case ("LIGHT-COUNT") is NOT proved.**
Script: `one-not/tools/kill_tests/mu_light.py` (run `python3 -I one-not/tools/kill_tests/mu_light.py one-not 9`, about 5 s).

## 0. Definitions used

D = points fixed to 0, Q = points fixed to 1, D ∩ Q = ∅. A set w is alive if S_w ∩ Q = ∅ and |S_w − D| ≥ 2;
base(D,Q) = Σ over alive w of (|S_w − D| − 1). An alive point is a point of an alive set outside D.
UC(D,Q) = OR gates g for which there are an alive set w, two points a ≠ b of S_w − D and a point Z with
Q ⊆ Z, Z ∩ (D ∪ S_w) = ∅, such that
* world 1: h(Z) = 0, C_1(g)(Z) = 0, C_1(g)(Z + e_a) = C_1(g)(Z + e_b) = 1; or
* world 0: C_0(g)(Z) = 0, h(Z + e_a) = h(Z + e_b) = 1, C_0(g)(Z + e_a) = C_0(g)(Z + e_b) = 1.

This is the restriction-closed count-set union (world 0 asks h = 1 only at the two witnessing atoms).
UC(D + v, Q) ⊆ UC(D,Q) and UC(D, Q + v) ⊆ UC(D,Q) hold by construction (a witness of the right side is a
witness of the left side). Moves: x_v := 0 costs deg(v) = #alive sets through v; x_v := 1 costs
Σ over alive w ∋ v of (|S_w − D| − 1). A move is "good" if |UC(D,Q) − UC(after)| ≥ cost.
"Light instance": h is not constant on the cube (D,Q) and h(Q + v) = 0 for every alive point v.

## 1. PROVED

**N1 (no-go for x_v := 0, count-set union).** There is a correct one-NOT circuit on which the gain of
x_v := 0 is deg(v) − 1 at EVERY point, for UC as above (and for the wider UC of `mu_induct.py`).
Circuit FANO-FORMULA: the 7 lines of the Fano plane; choose a bijection line → "last" point on it (a
perfect matching of the incidence graph; here last = 0,3,5,1,4,6,2 for the lines 012, 034, 056, 135, 146,
236, 245); line {a,b,c} with last point c is computed as g1 = x_a ∨ x_b, g2 = g1 ∨ x_c; add h = x_0 x_1 x_2
and an unused NOT gate. 17 gates, 14 OR gates, base 14, |UC| = 14.
*Proof.* The NOT gate is unused, so C_0 = C_1 = real on the 14 OR gates. Every point v is last on exactly
one of its three lines. Line with v last: g1 = x_a ∨ x_b keeps its witness (Z = ∅, world 1; h(∅) = 0), and
g2 restricted to x_v = 0 is again x_a ∨ x_b, so g2 keeps the witness (Z = ∅, atoms a, b). Both stay in
UC(v). Line {v,b,c} with v not last: g1 = x_v ∨ x_b has only the atoms v, b, so it leaves; g2 ≥ x_b ∨ x_c
(or contains them after restriction) stays. Gates of lines not through v keep witnesses with Z = ∅.
Gain = 2 < 3. ∎ (Machine check: first line of the script output.)
Cause: after x_v := 0 a gate may become a COPY of an earlier gate and still be counted. So no rule for
choosing v can rescue the x_v := 0 induction for a union of count sets; a repair must count something
else (distinct restricted functions, or first-merge gates, see N4). x_v := 1 is good at all 7 points there.

**N2 (Lemma C0, a sufficient condition for the x_v := 1 gain).** If C_0(g)(Q ∪ {v}) = 1 then
g ∉ UC(D, Q ∪ {v}). Hence gain of x_v := 1 ≥ #{g ∈ UC(D,Q) : C_0(g)(Q + v) = 1}.
*Proof.* C_0(g) is monotone and C_0(g) ≤ C_1(g), so both faces of g are 1 at every Z ⊇ Q + v; a witness
needs a face that is 0 at such a Z. ∎
(If only C_1(g)(Q + v) = 1, g has no world-1 witness after the move, but may keep world-0 witnesses.)
Tested: this count alone reaches the cost at some alive v on 3,723 of 3,891 light instances; not enough.

**N3 (free variables).** If v lies in no alive set, both moves at v cost 0 and UC(after) ⊆ UC(before), so
MU for the instance follows from MU after the move. In particular, if a variable outside every alive set
has h(Q + v) = 1, MU reduces to the monotone case C_0 on the cube Q + v. So in the open case one may
assume every free variable is fixed.

**N4 (paper proof, NOT corpus-tested; NOT-free gate lists only).** Let FM = OR gates γ for which there are
a set w, a pair a,b ∈ S_w and a Z avoiding S_w with: γ is the FIRST wire in circuit order with γ(Z) = 0
and γ ≥ x_a ∨ x_b. Then for a monotone circuit and every point v, |FM − FM(x_v := 0)| ≥ deg(v), and
FM(x_v := 0) ⊆ FM; so |FM| ≥ base by induction on points.
*Proof.* For w ∋ v let γ_w be the first wire with γ ≤ o_w that is ≥ x_v ∨ x_u for some u ∈ S_w − v (exists:
the output). If γ_w = s ∧ t, the input that is ≤ o_w is an earlier such wire. So γ_w = s ∨ t with s, t ≤ o_w;
say s ≥ x_v; by firstness s ≱ x_u for u ∈ S_w − v, and t ≱ x_v. γ_w is in FM (pair v,u, Z = top_w).
Suppose γ_w is first for (a,b,Z') with a,b ≠ v after the restriction: γ_w ≤ o_w gives a,b ∈ S_w, so
t ≥ x_a ∨ x_b on x_v = 0 and t(Z') = 0, and t is earlier: contradiction. Injective: x_v ∨ x_u ≤ γ_w ≤ o_w
fixes w. ∎ The coordinator's warning stands: unions of pure MERGE classes fail MU on cxMU_dd, so N4 is
recorded only as the reason why "first" repairs N1 in the monotone case; I did not extend it to one NOT.

## 2. TESTED only (mu_light.py: 71 corpus circuits + FANO-FORMULA + JUNK; every (D,Q) for n ≤ 7, 2,500 sampled otherwise)

| Case of the restricted instance | instances | MU | x:=1 good at every alive point | at some | x:=0 at some |
|---|---|---|---|---|---|
| h constant on the cube | 15,685 | all | 15,684 | all | all |
| some alive point heavy | 9,130 | all | 9,063 | all | 9,127 |
| light (LIGHT-COUNT, my case) | 3,891 | all | 3,888 | **all** | 3,890 |

* x_v := 1 at a heavy alive v: good on 13,164 of 13,164 (front A2's case, here for UC).
* Light case: 11,105 of 11,108 alive points are good for x_v := 1. The 3 bad points:
  dmax2_smallest_ess_k4e_clean_2721 with D = {3}, v = 0 (gain 1, cost 2);
  JUNK with D = ∅ and D = {4}, v = 0 (gain 1, cost 2).
* Rule "alive v of least h-influence (fewest points of the cube where h depends on x_v), ties by index"
  picks a good point on 3,891 of 3,891 light instances. Evidence is thin: only 3 bad points exist to test it.
* x_v := 0 has no good point on scaffold_certs.json:2 (and two restrictions of it) and on FANO-FORMULA.
  scaffold_certs.json:2 is "the one circuit": gate 7 = h ∧ ¬h, gate 8 = x_1 ∨ gate 7 has C_1 = x_0 ∨ x_1 ∨ x_3,
  and gates 8, 9, 10, 11 are all world-1 "merges" of the two heavy points 0, 3 (virtual atoms in U), so they
  stay in UC after any deletion.

JUNK (hand-built, correct, n = 5): sets {0,1,2}, {1,3}, {2,4}; gates 5 = x0∧x3 (= h), 6 = x0∧x4, 7 = NOT 5
(unused), 8 = x1∨5, 9 = x2∨6, 10 = 8∨9, 11 = 10∨x0, 12 = x1∨x3, 13 = x2∨x4. After x_0 := 1 the gates 8, 9, 10
become merges of {1,3} / {2,4}; only gate 11 leaves UC. So "every light point is good" is false.

## 3. OPEN

LIGHT-COUNT: in a light instance, some alive v has |UC(D,Q) − UC(D,Q + v)| ≥ Σ_{alive w ∋ v} (|S_w − D| − 1).
Not proved; no proved rule for v. Smallest obstructions to "every v": JUNK (v = 0; gates 8, 9, 10) and
dmax2…2721 at D = {3} (v = 0; gates 10 and 14, C_0 = x2 ∨ x0x1 ∨ x0x3, keep a world-0 witness for {1,2} at
Z = {0}). What a proof needs: for each alive w ∋ v, |S_w − D| − 1 gates with NO witness at any Z ∋ v for a
set avoiding v; Lemma C0 gives the gates with C_0 ≥ x_v on the cube, which is short on 168 light instances.
