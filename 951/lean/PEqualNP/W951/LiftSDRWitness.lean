import PEqualNP.W951.PureGP

/-!
# LiftSDRWitness: kernel-checked LiftSDR certificates for the barrier suite

The barrier suite (`951/data/witnesses`: `cxMU_dd`, `cxMU_clean2`, `cxMU_clean2_DD`, `cx44_1_junk`;
coord 64776ce; front C 12:17) consists of correct one-NOT circuits with NO pure SDR (for `cxMU_dd` and
`cxMU_clean2_DD` even MU over the pure menus fails). Front C reports GP-SDRs on all of them. Here each one
gets a LiftSDR (the official target with MUL since owner ~12:27) from GP test systems (`gpLTS b z A`, PureGP.lean),
found by `951/tools/sdrcert/lift_export.py` (Python finds, Lean checks): each system checked valid through
`gpLTS_valid` (`decide` on its three conditions), its class recomputed in the lift (`ltsCls`, `decide`) and
equal to a literal, the literals pairwise disjoint (`liftSDR_of_cert`). With them the correctness of each
circuit (all `2^7` inputs), the 951 set conditions and the NOT gate are kernel-checked (`*_correct`).

So the barriers to PureSDR and to pure-menu MU are NOT barriers to LiftSDR, hence not to MUL.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- **Certificates**: lifted test systems `t`, valid, whose classes are the literals `M w`, pairwise
disjoint. -/
theorem liftSDR_of_cert {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (p : ℕ) (t : Fin m → LTS n) (M : Fin m → Finset ℕ)
    (hv : ∀ w, LTSValid gates p (S w) (out w) (t w)) (hM : ∀ w, ltsCls gates p (S w) (t w) = M w)
    (hdisj : ∀ w w', w ≠ w' → Disjoint (M w) (M w')) : LiftSDR S gates out p :=
  ⟨t, hv, fun w w' hww => by rw [hM w, hM w']; exact hdisj w w' hww⟩

/-! ### cx441Junk: n = 7, 59 gates (NOT gate 3), 2 sets; GP worlds C1, C1 -/

def lCx441JunkGates : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [14, 19]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [14, 21]⟩, ⟨GateOp.and, [10, 3]⟩, ⟨GateOp.and, [11, 4]⟩, ⟨GateOp.or, [23, 24]⟩, ⟨GateOp.or, [14, 25]⟩, ⟨GateOp.and, [10, 6]⟩, ⟨GateOp.and, [12, 1]⟩, ⟨GateOp.or, [27, 28]⟩, ⟨GateOp.or, [14, 29]⟩, ⟨GateOp.and, [12, 2]⟩, ⟨GateOp.and, [11, 5]⟩, ⟨GateOp.or, [31, 32]⟩, ⟨GateOp.and, [12, 3]⟩, ⟨GateOp.and, [11, 6]⟩, ⟨GateOp.or, [34, 35]⟩, ⟨GateOp.or, [33, 36]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [5, 2]⟩, ⟨GateOp.and, [38, 39]⟩, ⟨GateOp.or, [0, 40]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [4, 1]⟩, ⟨GateOp.and, [42, 43]⟩, ⟨GateOp.or, [41, 44]⟩, ⟨GateOp.and, [8, 3]⟩, ⟨GateOp.and, [7, 6]⟩, ⟨GateOp.or, [46, 47]⟩, ⟨GateOp.or, [45, 48]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.or, [50, 1]⟩, ⟨GateOp.or, [51, 2]⟩, ⟨GateOp.or, [52, 3]⟩, ⟨GateOp.and, [10, 53]⟩, ⟨GateOp.or, [54, 7]⟩, ⟨GateOp.and, [8, 49]⟩, ⟨GateOp.or, [55, 56]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.or, [58, 4]⟩, ⟨GateOp.or, [59, 5]⟩, ⟨GateOp.or, [60, 6]⟩, ⟨GateOp.and, [10, 61]⟩, ⟨GateOp.or, [62, 8]⟩, ⟨GateOp.and, [7, 49]⟩, ⟨GateOp.or, [63, 64]⟩]
def lCx441JunkS : Fin 2 → Finset (Fin 7) := ![{0, 1, 2, 3}, {0, 4, 5, 6}]
def lCx441JunkOut : Fin 2 → ℕ := ![57, 65]
def lCx441JunkT : Fin 2 → LTS 7 := ![gpLTS true (canonPt {}) ![{0}, {1}, {2, 4}, {3, 5}, {}, {}, {}], gpLTS true (canonPt {1}) ![{0}, {}, {}, {}, {4}, {5}, {2, 6}]]
def lCx441JunkM : Fin 2 → Finset ℕ := ![{15, 16, 17}, {19, 20, 21}]

set_option maxRecDepth 100000 in
theorem lCx441Junk_valid : ∀ w, LTSValid lCx441JunkGates 3 (lCx441JunkS w) (lCx441JunkOut w) (lCx441JunkT w) := by
  intro w
  fin_cases w
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem lCx441Junk_cls : ∀ w, ltsCls lCx441JunkGates 3 (lCx441JunkS w) (lCx441JunkT w) = lCx441JunkM w := by decide

theorem lCx441Junk : LiftSDR lCx441JunkS lCx441JunkGates lCx441JunkOut 3 :=
  liftSDR_of_cert _ _ _ _ lCx441JunkT lCx441JunkM lCx441Junk_valid lCx441Junk_cls (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `cx441Junk`: correct, (1,1)-disjoint sets of size at least 2, one NOT gate (gate 3), LiftSDR. -/
theorem lCx441Junk_correct :
    (∀ (w : Fin 2) (x : Fin 7 → Bool),
      val lCx441JunkGates x (lCx441JunkOut w) = decide (∃ v ∈ lCx441JunkS w, x v = true)) ∧
    (∀ w, 2 ≤ (lCx441JunkS w).card) ∧
    (∀ a b : Fin 2, a ≠ b → (lCx441JunkS a ∩ lCx441JunkS b).card ≤ 1) ∧
    lCx441JunkGates[3]? = some ⟨GateOp.not, [9]⟩ ∧
    LiftSDR lCx441JunkS lCx441JunkGates lCx441JunkOut 3 :=
  ⟨by decide, by decide, by decide, rfl, lCx441Junk⟩

/-! ### cxMUClean2: n = 7, 30 gates (NOT gate 5), 2 sets; GP worlds C1, C1 -/

def lCxMUClean2Gates : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [13, 5]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [15, 6]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [12, 17]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [22, 24]⟩, ⟨GateOp.or, [0, 25]⟩, ⟨GateOp.and, [26, 2]⟩, ⟨GateOp.or, [7, 27]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [12, 29]⟩, ⟨GateOp.or, [28, 30]⟩, ⟨GateOp.or, [31, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [12, 33]⟩, ⟨GateOp.and, [9, 34]⟩, ⟨GateOp.or, [35, 10]⟩]
def lCxMUClean2S : Fin 2 → Finset (Fin 7) := ![{0, 1, 2, 3}, {0, 4, 5, 6}]
def lCxMUClean2Out : Fin 2 → ℕ := ![32, 36]
def lCxMUClean2T : Fin 2 → LTS 7 := ![gpLTS true (canonPt {}) ![{0, 4}, {1}, {2}, {3}, {}, {}, {}], gpLTS true (canonPt {}) ![{0}, {}, {}, {}, {4}, {5}, {6}]]
def lCxMUClean2M : Fin 2 → Finset ℕ := ![{8, 9, 12}, {10, 11, 26}]

set_option maxRecDepth 100000 in
theorem lCxMUClean2_valid : ∀ w, LTSValid lCxMUClean2Gates 5 (lCxMUClean2S w) (lCxMUClean2Out w) (lCxMUClean2T w) := by
  intro w
  fin_cases w
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem lCxMUClean2_cls : ∀ w, ltsCls lCxMUClean2Gates 5 (lCxMUClean2S w) (lCxMUClean2T w) = lCxMUClean2M w := by decide

theorem lCxMUClean2 : LiftSDR lCxMUClean2S lCxMUClean2Gates lCxMUClean2Out 5 :=
  liftSDR_of_cert _ _ _ _ lCxMUClean2T lCxMUClean2M lCxMUClean2_valid lCxMUClean2_cls (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `cxMUClean2`: correct, (1,1)-disjoint sets of size at least 2, one NOT gate (gate 5), LiftSDR. -/
theorem lCxMUClean2_correct :
    (∀ (w : Fin 2) (x : Fin 7 → Bool),
      val lCxMUClean2Gates x (lCxMUClean2Out w) = decide (∃ v ∈ lCxMUClean2S w, x v = true)) ∧
    (∀ w, 2 ≤ (lCxMUClean2S w).card) ∧
    (∀ a b : Fin 2, a ≠ b → (lCxMUClean2S a ∩ lCxMUClean2S b).card ≤ 1) ∧
    lCxMUClean2Gates[5]? = some ⟨GateOp.not, [11]⟩ ∧
    LiftSDR lCxMUClean2S lCxMUClean2Gates lCxMUClean2Out 5 :=
  ⟨by decide, by decide, by decide, rfl, lCxMUClean2⟩

/-! ### cxMUClean2DD: n = 7, 33 gates (NOT gate 5), 2 sets; GP worlds C1, C1 -/

def lCxMUClean2DDGates : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [13, 5]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [15, 6]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [12, 17]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [22, 24]⟩, ⟨GateOp.or, [0, 25]⟩, ⟨GateOp.and, [26, 2]⟩, ⟨GateOp.or, [7, 27]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [12, 29]⟩, ⟨GateOp.or, [28, 30]⟩, ⟨GateOp.or, [31, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [12, 33]⟩, ⟨GateOp.and, [9, 34]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [12, 36]⟩, ⟨GateOp.or, [10, 37]⟩, ⟨GateOp.or, [35, 38]⟩]
def lCxMUClean2DDS : Fin 2 → Finset (Fin 7) := ![{0, 1, 2, 3}, {0, 4, 5, 6}]
def lCxMUClean2DDOut : Fin 2 → ℕ := ![32, 39]
def lCxMUClean2DDT : Fin 2 → LTS 7 := ![gpLTS true (canonPt {}) ![{0, 4}, {1}, {2}, {3}, {}, {}, {}], gpLTS true (canonPt {}) ![{0}, {}, {}, {}, {4}, {5}, {6}]]
def lCxMUClean2DDM : Fin 2 → Finset ℕ := ![{8, 9, 12}, {10, 11, 26}]

set_option maxRecDepth 100000 in
theorem lCxMUClean2DD_valid : ∀ w, LTSValid lCxMUClean2DDGates 5 (lCxMUClean2DDS w) (lCxMUClean2DDOut w) (lCxMUClean2DDT w) := by
  intro w
  fin_cases w
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem lCxMUClean2DD_cls : ∀ w, ltsCls lCxMUClean2DDGates 5 (lCxMUClean2DDS w) (lCxMUClean2DDT w) = lCxMUClean2DDM w := by decide

theorem lCxMUClean2DD : LiftSDR lCxMUClean2DDS lCxMUClean2DDGates lCxMUClean2DDOut 5 :=
  liftSDR_of_cert _ _ _ _ lCxMUClean2DDT lCxMUClean2DDM lCxMUClean2DD_valid lCxMUClean2DD_cls (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `cxMUClean2DD`: correct, (1,1)-disjoint sets of size at least 2, one NOT gate (gate 5), LiftSDR. -/
theorem lCxMUClean2DD_correct :
    (∀ (w : Fin 2) (x : Fin 7 → Bool),
      val lCxMUClean2DDGates x (lCxMUClean2DDOut w) = decide (∃ v ∈ lCxMUClean2DDS w, x v = true)) ∧
    (∀ w, 2 ≤ (lCxMUClean2DDS w).card) ∧
    (∀ a b : Fin 2, a ≠ b → (lCxMUClean2DDS a ∩ lCxMUClean2DDS b).card ≤ 1) ∧
    lCxMUClean2DDGates[5]? = some ⟨GateOp.not, [11]⟩ ∧
    LiftSDR lCxMUClean2DDS lCxMUClean2DDGates lCxMUClean2DDOut 5 :=
  ⟨by decide, by decide, by decide, rfl, lCxMUClean2DD⟩

/-! ### cxMUDd: n = 7, 36 gates (NOT gate 5), 2 sets; GP worlds C0, C1 -/

def lCxMUDdGates : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [13, 5]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [15, 6]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [12, 17]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [22, 24]⟩, ⟨GateOp.or, [0, 25]⟩, ⟨GateOp.and, [26, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [12, 28]⟩, ⟨GateOp.and, [7, 29]⟩, ⟨GateOp.or, [30, 27]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [12, 32]⟩, ⟨GateOp.or, [31, 33]⟩, ⟨GateOp.or, [34, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [12, 36]⟩, ⟨GateOp.and, [9, 37]⟩, ⟨GateOp.or, [5, 1]⟩, ⟨GateOp.and, [12, 39]⟩, ⟨GateOp.or, [38, 40]⟩, ⟨GateOp.or, [41, 10]⟩]
def lCxMUDdS : Fin 2 → Finset (Fin 7) := ![{0, 1, 2, 3}, {0, 4, 5, 6}]
def lCxMUDdOut : Fin 2 → ℕ := ![35, 42]
def lCxMUDdT : Fin 2 → LTS 7 := ![gpLTS false (canonPt {3}) ![{0, 3, 6}, {1, 3}, {2, 3}, {3, 4}, {}, {}, {}], gpLTS true (canonPt {}) ![{0}, {}, {}, {}, {3, 4}, {5}, {6}]]
def lCxMUDdM : Fin 2 → Finset ℕ := ![{9, 12, 19}, {8, 10, 11}]

set_option maxRecDepth 100000 in
theorem lCxMUDd_valid : ∀ w, LTSValid lCxMUDdGates 5 (lCxMUDdS w) (lCxMUDdOut w) (lCxMUDdT w) := by
  intro w
  fin_cases w
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · exact gpLTS_valid _ _ _ _ _ _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem lCxMUDd_cls : ∀ w, ltsCls lCxMUDdGates 5 (lCxMUDdS w) (lCxMUDdT w) = lCxMUDdM w := by decide

theorem lCxMUDd : LiftSDR lCxMUDdS lCxMUDdGates lCxMUDdOut 5 :=
  liftSDR_of_cert _ _ _ _ lCxMUDdT lCxMUDdM lCxMUDd_valid lCxMUDd_cls (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `cxMUDd`: correct, (1,1)-disjoint sets of size at least 2, one NOT gate (gate 5), LiftSDR. -/
theorem lCxMUDd_correct :
    (∀ (w : Fin 2) (x : Fin 7 → Bool),
      val lCxMUDdGates x (lCxMUDdOut w) = decide (∃ v ∈ lCxMUDdS w, x v = true)) ∧
    (∀ w, 2 ≤ (lCxMUDdS w).card) ∧
    (∀ a b : Fin 2, a ≠ b → (lCxMUDdS a ∩ lCxMUDdS b).card ≤ 1) ∧
    lCxMUDdGates[5]? = some ⟨GateOp.not, [11]⟩ ∧
    LiftSDR lCxMUDdS lCxMUDdGates lCxMUDdOut 5 :=
  ⟨by decide, by decide, by decide, rfl, lCxMUDd⟩

end PEqualNP.Outside.L_meta_951_aux
