# The DD core (U-game lost): data (cTAHG, 2026-11-24, coord 14:05)

Question (coord): on the circuits whose lifted outputs LOSE the U-game (open part (X) of Theorem G), which gates make the
game lost, and are they removable? Tools: `research/one-not/tools/kill_tests/ddcore.py`, `ugame_rfacts.py` (U-game vs R1–R5′, R+ of
`f2_rplus_all.py`, R+ over every wire including inputs and every nonempty reader set).

## 1. The two barrier circuits are already excluded by Lean MinCE facts (CHECKED)
- **cxMU_dd** (n = 7, s = 36, sets {0,1,2,3}, {0,4,5,6}, h = x1 ∨ x4). R1–R5′ hold, but **R+ fails 178 times**. Example:
  substituting x0 := 0 into the readers and(0,2), or(0,25), or(0,4) (wires 13, 26, 28) keeps every output correct. That is
  exactly the situation `MinCE.observable` (MinCERed.lean) excludes. The outputs have C_1 = s ∨ h; every N-dependent gate except
  N has a private cone; gates 26, 27 are C_0-equal (R7 territory). (The 14:05 BOARD line "cxMU_dd violates only R7" holds only
  for an R+ check without input wires.)
- **cx44_1_junk** (n = 7, s = 59): 27 dead gates (R4). Its live part cx44_1 (32 gates, = front-match__fc__cx44_1) fails **R2**
  (and(1,2) and and(4,5) computed twice) and R+ (36). DD-normal outputs, private N-cones.

## 2. The genuine DD core: R-clean and U-game lost (CHECKED)
On 88 correct one-NOT circuits in the repo: U-game won on 76; R-clean (R1–R5′ and R+ all hold) on 3; **R-clean and LOST: 1**:
- **cxT2 (fc)**: `research/one-not/tools/w951/tests/instances/front-match__fc__cxT2.json`, n = 9, s = 29, base 9.
  - Sets: a triangle {0,2,3,4}, {0,1,5,6}, {1,2,7,8}; h = x0 ∨ x1 ∨ x2, the three shared points.
  - All three outputs DD-normal (C_0 = s ∧ h, C_1 = s ∨ h).
  - N-cone SHARED: N ∨ x-stuff (wire 23) is in all three cones; wires 24, 25 are in two each. Wires 26–28 and 31, 34, 37 are
    private. No N-dependent gate is C_0- or C_1-equal, so a C_0/C_1-equality lemma (R7, private or shared) does not touch it.
  - Yet **MergeSDR holds**: real merge sets {14,16,19}, {9,32,33}, {10,35,36} are pairwise disjoint, so LiftSDR holds
    (`liftSDR_of_mergeSDR`; kernel certificate earlier in SDRCert batch 2). The disjointness is NOT Theorem U; it is the
    first-merge structure (Lemma T / 2G-LIFT territory: three sets, triangle, the shared points heavy).

## 3. Consequence
"A MinCE whose U-game is lost has a removable gate" is FALSE as a consequence of the local MinCE facts: cxT2 (fc) is correct,
satisfies R1–R5′ and R+, and loses the U-game. Excluding (X) from a MinCE therefore needs either:
(i) a disjointness mechanism beyond Theorem U, i.e. the first-merge structure (Lemma T; 2G-LIFT is the k = 2 piece, already
    in Lean as `twoGate_lift`), which proves LiftSDR / MergeSDR on cxT2-type cores; or
(ii) `gates < base` itself (ElimStep: every closing step at the top is 951-strength).
cxMU_dd and cx44_1 need neither: R+ / R2 already exclude them.

## 4. Desktop Coord's R7 forms (14:06 / 14:10) tested (CHECKED, research/tools/kill_tests/rewire_r6.py)
- **R7 (C_b-equality, private or shared cone) and R7-ODC** are instances of R+ with u = N. cxT2 (fc) has 0 R+ violations over
  every wire and every reader set, so no constant on any set of N's edges keeps it correct.
- **R7-REWIRE, generalised to every edge (R6):** rewire input `pos` of gate r to an existing wire f outside desc(r); a rewire
  that keeps every output correct and leaves a gate unread saves a gate without a new NOT, contradicting minimality.
  - cxT2 (fc): 1,679 candidates, 4 correct, 0 gate-saving. It is locally irreducible.
  - cxMU_dd: 633 gate-saving rewires. cx44_1: 40.
  - **MATCH-C (k = 7): 3 gate-saving rewires.** The NOT may read wire 64 = x_{u_0} ∨ x_{a_0} (the output of P_0) instead of
    h = U ∨ V, and every output stays correct (o_A = (X_A ∧ ¬(x_{u_0} ∨ x_{a_0})) ∨ f_A = x_y ∨ U, checked), so the h tree is spare.
- **Consequence for 6217a97 (F2 step at non-local cubes refuted under R1–R5′, R+):** MATCH-C is NOT rewire-irreducible.
  A greedy R6 reduction (55 → 45 gates) keeps one NOT and a non-local h for 10 rewires. The F2 step still fails at Q = ∅ at
  55..50 gates, holds at 49..46 gates, and at 45 the NOT is dead (monotone circuit). So MATCH-C is not a witness against the
  step in the R6-irreducible class; whether one exists is OPEN.

## 5. How MergeSDR beats the lost U-game on cxT2 (fc) (CHECKED; first step of the triangle analysis)
108 pairwise disjoint choices of real merge sets exist. A typical one MIXES worlds:
- set {0,2,3,4} at z = {1,5,6,7,8} (h = 1, world 0, NOT gate 0): merges {14, 16, 19}, i.e. junk AND/OR gates of the layer
  x1x3 ∨ x2x5 ∨ x0x7 ∨ x1x4 ∨ x2x6 ∨ x0x8;
- sets {0,1,5,6} at z = {3,4,7,8} and {1,2,7,8} at z = {3,4,5,6} (h = 0, world 1): merges {9, 32, 33} and {10, 35, 36}.
By Theorem D a pure world-0 system and a pure world-1 system never certify each other, so this disjointness is NOT monotonicity
(Theorem U). It is value-specific first-merge structure: e.g. gate 14 = x1x3 ∨ x2x5 is 0 at z = {3,4,7,8} and has trace {1}
only on the atoms of {0,1,5,6}, so it never merges there. The plain DD circuits of the (X) pairs (lift_obstruction.dd_circuit)
compute each OR(S_w) as a private chain and have a MergeSDR trivially, so the hard DD instances are exactly those whose
outputs share junk structure (cxT2-type). A proof for the DD core must therefore control traces of shared gates across worlds
(Lemma T across two frames). Open.
