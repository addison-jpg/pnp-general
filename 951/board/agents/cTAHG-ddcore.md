# The DD core (U-game lost): data (cTAHG, 2026-11-24, coord 14:05)

Question (coord): on the circuits whose lifted outputs LOSE the U-game (open part (X) of Theorem G), which gates make the
game lost, and are they removable? Tools: `951/tools/kill_tests/ddcore.py`, `ugame_rfacts.py` (U-game vs R1–R5′, R+ of
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
- **cxT2 (fc)**: `951/tools/w951/tests/instances/front-match__fc__cxT2.json`, n = 9, s = 29, base 9.
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
