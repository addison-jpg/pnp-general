import PEqualNP.W951.MergeDual
import PEqualNP.W951.MergeWorld2

/-! Heavy: heavy points and the heavy split of MergeFrac (coord re-aim 08:23, front's case split,
board agents/front-heavy.md).

With the NOT gate at `p` reading `h = hval gates p`, a point `v` is **heavy** when `h ≥ x_v`,
i.e. `h (e_v) = 1` (`h` is monotone). No current lemma excludes heavy points at a MinCE (front;
gAdyD: every essential clean circuit with `s - base ≤ 4` has one inside a set), so MergeFrac is
split into two cases:
* Case I, no heavy point in any set: the refined no-mixed form (`RefinedNoMixedFrac`, MergeWorld2;
  with no heavy set it is `NoMixedFrac`, price form `NoMixedPrice`, world split
  `noMixedPrice_iff_worlds`, MergeDual).
* Case II, a heavy `v`: every set `b ∌ v` is pinned at its own base point `Zof (S b)`, and only the
  star of `v` (the sets containing `v`) chooses fractionally among its zero points (`HeavySplit`).

Results.
(a) `Heavy` is the point form of MergeWorld2's `HeavySet` (`heavySet_iff`).
    `heavy_val_C0`: under `x_v := 1` the circuit is pure `C0` (NOT `:= 0`), on every wire.
    `heavy_world0` (every point with `x_v = 1` is world-0), `heavy_pinned_C0` (the pinned merge set of
    a set `R ∌ v` is the merge set of the monotone circuit `C0`), `heavy_star_not_world1` (a set
    containing `v` has no world-1 zero point).
(b) `heavyPts`, `HeavySplit`, `HeavySplitPrice`, `heavySplit_iff_price` (LP duality),
    `mergeFrac_of_heavySplit`, `no_minCE_of_heavyCases` (Case II for some point, or Case I in the
    refined form, at every MinCE closes `no_minCE`).
(d) Case I price form: `refinedPts` (heavy sets: all zero points; others: non-mixed zero points),
    `refinedNoMixedFrac_iff_mergeFracOn`, `refinedPts_nonempty` (no extra hypothesis, by
    `exists_nonMixed_of_not_heavy`), `RefinedNoMixedPrice`, `refinedNoMixedFrac_iff_price`,
    `no_minCE_of_refinedNoMixedPrice`.
(b') Case II, float form (front's v2 after the pinned rule was refuted on 320 essential circuits):
    `heavyFloatPts` (star of `v`: all zero points; other sets: zero points with `x_v = 1`, all world-0),
    `HeavySplitFloat`, `HeavySplitFloatPrice`, `heavySplitFloat_iff_price`,
    `heavySplitFloat_of_heavySplit` (pinned ⇒ float), `mergeFrac_of_heavySplitFloat`,
    `heavyFloatPts_v`, `heavy_float_C0` (floating sets read only `C0` merge sets),
    `no_minCE_of_heavyFloatCases`.
(c) The pinned disjointness that Case II would need ("`C0` merge sets of different sets at their own
    bases `Zof` are disjoint") FAILS for clean circuits: `pinned_collision_clean` is a monotone circuit
    on 4 inputs computing `x0 ∨ x1` and `x2 ∨ x3` with no copy gate (the `MinCE.clean` condition), all
    gates of fan-in 2, in which the gate `(x0 ∧ x2) ∨ (x1 ∧ x3)` is the merge of both sets at their
    bases. So a proof of Case II must use more than cleanliness (gate-minimality of a MinCE, or the
    NOT gate), or let the sets `b ∌ v` float too. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## (a) Heavy points: pure `C0` on `{x_v = 1}` -/

theorem eof_le {n : ℕ} {v : Fin n} {x : Fin n → Bool} (hx : x v = true) : eof v ≤ x := by
  intro c
  by_cases h : c = v
  · subst h; rw [hx]; exact Bool.le_true _
  · simp [eof, h]

/-- `v` is **heavy** for the NOT gate at `p`: `h ≥ x_v`, i.e. `h (e_v) = 1`. -/
def Heavy {n : ℕ} (gates : List Gate) (p : ℕ) (v : Fin n) : Prop :=
  hval gates p (eof v) = true

/-- A heavy set (MergeWorld2) is a set containing a heavy point. -/
theorem heavySet_iff {n : ℕ} (gates : List Gate) (p : ℕ) (S : Finset (Fin n)) :
    HeavySet gates p S ↔ ∃ v ∈ S, Heavy gates p v :=
  Iff.rfl

section HeavyFacts

variable {n : ℕ} {gates : List Gate} {p : ℕ} (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) {v : Fin n}
  (hv : Heavy gates p v)

include hg hU hN hv

/-- A heavy `v` forces `h = 1` on the half-cube `{x_v = 1}`. -/
theorem heavy_hval {x : Fin n → Bool} (hx : x v = true) : hval gates p x = true :=
  hval_mono gates p hp hg hU hN (eof_le hx) hv

/-- **(a) Under `x_v := 1` the circuit is pure `C0`** (the NOT gate is `0`): every wire agrees with
the monotone circuit `C0` at every point with `x_v = 1`. -/
theorem heavy_val_C0 {x : Fin n → Bool} (hx : x v = true) (i : ℕ) :
    val gates x i = val (C0 gates) x i := by
  have h := val_wld_false_of_hval gates p hp hU hN x (heavy_hval hp hg hU hN hv hx) i
  simpa [wld] using h.symm

/-- Every point with `x_v = 1` is a world-0 point. -/
theorem heavy_world0 {z : Fin n → Bool} (hz : z v = true) : World0 gates z :=
  (world0_iff_hval hU hp hN z).mpr (heavy_hval hp hg hU hN hv hz)

/-- **Pinned sets are monotone**: for a set `R ∌ v`, the merge set at its base `Zof R` (which has
`x_v = 1`) is the merge set of the monotone circuit `C0`. -/
theorem heavy_pinned_C0 {R : Finset (Fin n)} (hvR : v ∉ R) :
    mergeSet gates R (Zof R) = mergeSet (C0 gates) R (Zof R) :=
  mergeSet_C0_of_world0 hg hU R (heavy_world0 hp hg hU hN hv (by simp [Zof, hvR]))

/-- **The star has no world-1 point**: a set containing `v` has no world-1 zero point
(`h (z + e_v) = 1`). -/
theorem heavy_star_not_world1 {R : Finset (Fin n)} (hvR : v ∈ R) (z : Fin n → Bool) :
    ¬ World1 gates R z :=
  HeavySet.not_world1 hg hU hp hN ⟨v, hvR, hv⟩ z

end HeavyFacts

/-! ## (b) Case II: the heavy split -/

section Split

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (v : Fin n)

open Classical in
/-- The allowed points of the heavy split: a set containing `v` keeps all its zero points; every
other set is pinned at its base point `Zof (S w)`. -/
noncomputable def heavyPts (w : Fin m) : Finset (Fin n → Bool) :=
  if v ∈ S w then zeroPts (S w) else {Zof (S w)}

theorem Zof_mem_zeroPts (R : Finset (Fin n)) : Zof R ∈ zeroPts R :=
  mem_zeroPts.mpr (Zof_zero R)

theorem heavyPts_nonempty (w : Fin m) : (heavyPts S v w).Nonempty := by
  classical
  unfold heavyPts
  split_ifs
  · exact zeroPts_nonempty _
  · exact Finset.singleton_nonempty _

theorem heavyPts_subset (w : Fin m) : heavyPts S v w ⊆ zeroPts (S w) := by
  classical
  unfold heavyPts
  split_ifs
  · exact le_rfl
  · exact Finset.singleton_subset_iff.mpr (Zof_mem_zeroPts _)

/-- **Case II (the heavy split)**: distributions with every set `b ∌ v` pinned at `Zof (S b)` and
the star of `v` choosing among its zero points, with every wire load `≤ 1`. -/
def HeavySplit : Prop :=
  MergeFracOn S gates (heavyPts S v)

/-- The price form of Case II: `∀ π ≥ 0, ∑_{w ∌ v} π(M_{Zof}(w)) + ∑_{w ∋ v} min_z π(M_z(w)) ≤
π(gates)` (written with the allowed points `heavyPts`). -/
def HeavySplitPrice : Prop :=
  MergePriceOn S gates (heavyPts S v) (heavyPts_nonempty S v)

/-- LP duality for Case II. -/
theorem heavySplit_iff_price : HeavySplit S gates v ↔ HeavySplitPrice S gates v :=
  mergeFracOn_iff_mergePriceOn (heavyPts_nonempty S v)

/-- Case II gives MergeFrac. -/
theorem mergeFrac_of_heavySplit (h : HeavySplit S gates v) : MergeFrac S gates :=
  (mergeFracOn_zeroPts_iff S gates).mp (mergeFracOn_mono (heavyPts_subset S v) h)

/-! ### Case II, float form (front's v2, coord 09:01): sets `b ∌ v` float inside `{x_v = 1}` -/

open Classical in
/-- The allowed points of the float form: a set containing `v` keeps all its zero points; every
other set keeps its zero points with `x_v = 1` (all world-0 when `v` is heavy, `heavy_world0`). -/
noncomputable def heavyFloatPts (w : Fin m) : Finset (Fin n → Bool) :=
  if v ∈ S w then zeroPts (S w) else (zeroPts (S w)).filter fun z => z v = true

theorem heavyPts_subset_float (w : Fin m) : heavyPts S v w ⊆ heavyFloatPts S v w := by
  classical
  unfold heavyPts heavyFloatPts
  split_ifs with hv
  · exact le_rfl
  · exact Finset.singleton_subset_iff.mpr
      (Finset.mem_filter.mpr ⟨Zof_mem_zeroPts _, by simp [Zof, hv]⟩)

theorem heavyFloatPts_nonempty (w : Fin m) : (heavyFloatPts S v w).Nonempty :=
  (heavyPts_nonempty S v w).mono (heavyPts_subset_float S v w)

theorem heavyFloatPts_subset (w : Fin m) : heavyFloatPts S v w ⊆ zeroPts (S w) := by
  classical
  unfold heavyFloatPts
  split_ifs
  · exact le_rfl
  · exact Finset.filter_subset _ _

/-- A floating point of a set `b ∌ v` has `x_v = 1`. -/
theorem heavyFloatPts_v {w : Fin m} (hvw : v ∉ S w) {z : Fin n → Bool}
    (hz : z ∈ heavyFloatPts S v w) : z v = true := by
  classical
  unfold heavyFloatPts at hz
  rw [ite_eq_right hvw] at hz
  exact (Finset.mem_filter.mp hz).2

/-- **Case II, float form**: the star of `v` floats over its zero points, every other set floats
over its zero points with `x_v = 1`, every wire load `≤ 1`. -/
def HeavySplitFloat : Prop :=
  MergeFracOn S gates (heavyFloatPts S v)

/-- The price form of the float form. -/
def HeavySplitFloatPrice : Prop :=
  MergePriceOn S gates (heavyFloatPts S v) (heavyFloatPts_nonempty S v)

/-- LP duality for the float form. -/
theorem heavySplitFloat_iff_price : HeavySplitFloat S gates v ↔ HeavySplitFloatPrice S gates v :=
  mergeFracOn_iff_mergePriceOn (heavyFloatPts_nonempty S v)

/-- The pinned form implies the float form. -/
theorem heavySplitFloat_of_heavySplit (h : HeavySplit S gates v) : HeavySplitFloat S gates v :=
  mergeFracOn_mono (heavyPts_subset_float S v) h

/-- The float form gives MergeFrac. -/
theorem mergeFrac_of_heavySplitFloat (h : HeavySplitFloat S gates v) : MergeFrac S gates :=
  (mergeFracOn_zeroPts_iff S gates).mp (mergeFracOn_mono (heavyFloatPts_subset S v) h)

end Split

/-- **The case split closes `no_minCE`**: if at every minimal counterexample either Case II holds for
some point (`HeavySplit`) or Case I holds in the refined form (`RefinedNoMixedFrac`, for the NOT
gate at some `p`), there is no minimal counterexample. -/
theorem no_minCE_of_heavyCases
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        (∃ v : Fin n, HeavySplit S gates v) ∨ ∃ p : ℕ, RefinedNoMixedFrac S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M => by
    rcases H n m S gates out M with ⟨v, hv⟩ | ⟨p, h⟩
    · exact mergeFrac_of_heavySplit S gates v hv
    · exact mergeFrac_of_refinedNoMixedFrac S gates p h

/-- **Floating sets are monotone**: with `v` heavy, a set `w ∌ v` at any of its floating points has
the merge set of the monotone circuit `C0` (the point has `x_v = 1`, so it is world-0). -/
theorem heavy_float_C0 {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate} {p : ℕ}
    (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) {v : Fin n}
    (hv : Heavy gates p v) {w : Fin m} (hvw : v ∉ S w) {z : Fin n → Bool}
    (hz : z ∈ heavyFloatPts S v w) :
    mergeSet gates (S w) z = mergeSet (C0 gates) (S w) z :=
  mergeSet_C0_of_world0 hg hU (S w) (heavy_world0 hp hg hU hN hv (heavyFloatPts_v S v hvw hz))

/-- **The case split, float form, closes `no_minCE`**: Case II in the float form for some point, or
Case I in the refined form, at every minimal counterexample. (Weaker hypothesis than
`no_minCE_of_heavyCases`, by `heavySplitFloat_of_heavySplit`.) -/
theorem no_minCE_of_heavyFloatCases
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        (∃ v : Fin n, HeavySplitFloat S gates v) ∨ ∃ p : ℕ, RefinedNoMixedFrac S gates p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M => by
    rcases H n m S gates out M with ⟨v, hv⟩ | ⟨p, h⟩
    · exact mergeFrac_of_heavySplitFloat S gates v hv
    · exact mergeFrac_of_refinedNoMixedFrac S gates p h

/-! ## (c) Pinned merge sets can collide in a clean circuit -/

/-- Inputs `x0..x3` (wires 0-3); gates: `4 = x0 ∧ x2`, `5 = x1 ∧ x3`, `6 = 4 ∨ 5`, `7 = 6 ∨ x0`,
`8 = 7 ∨ x1` (`= x0 ∨ x1`), `9 = 6 ∨ x2`, `10 = 9 ∨ x3` (`= x2 ∨ x3`). -/
def collisionGates : List Gate :=
  [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [9, 3]⟩]

/-- The sets `{0, 1}` and `{2, 3}`. -/
def collisionSets : Fin 2 → Finset (Fin 4) := ![{0, 1}, {2, 3}]

/-- The outputs: wire `8` for `{0, 1}`, wire `10` for `{2, 3}`. -/
def collisionOut : Fin 2 → ℕ := ![8, 10]

set_option maxRecDepth 4000 in
/-- **Pinned `C0` merge sets of different sets can share a gate in a clean circuit.** A monotone
circuit (so `C0 gates = gates`) with AND/OR gates of fan-in 2, computing `OR(S w)` at `out w` for two
disjoint sets of size 2, with no gate computing the same function as an earlier wire (`MinCE.clean`),
in which wire `6 = (x0 ∧ x2) ∨ (x1 ∧ x3)` is in the `C0` merge set of BOTH sets at their own bases
`Zof (S w)`. So the disjointness of pinned merge sets needs more than cleanliness. -/
theorem pinned_collision_clean :
    (∀ g ∈ collisionGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ w, 2 ≤ (collisionSets w).card) ∧
    (∀ a b : Fin 2, a ≠ b → (collisionSets a ∩ collisionSets b).card ≤ 1) ∧
    (∀ (w : Fin 2) (x : Fin 4 → Bool),
      val collisionGates x (collisionOut w) = decide (∃ v ∈ collisionSets w, x v = true)) ∧
    (∀ k j : ℕ, k < collisionGates.length → j < 4 + k →
      ¬ ∀ x : Fin 4 → Bool, val collisionGates x (4 + k) = val collisionGates x j) ∧
    6 ∈ mergeSet (C0 collisionGates) (collisionSets 0) (Zof (collisionSets 0)) ∧
    6 ∈ mergeSet (C0 collisionGates) (collisionSets 1) (Zof (collisionSets 1)) := by
  refine ⟨?_, by decide, by decide, by decide, ?_, by decide, by decide⟩
  · intro g hg
    simp only [collisionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro k j hk hj
    simp only [collisionGates, List.length_cons, List.length_nil] at hk
    interval_cases k <;> interval_cases j <;> decide

/-! ## Case I: the price form of the refined no-mixed target -/

section Refined

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ)

open Classical in
/-- The allowed points of `RefinedNoMixedFrac` (MergeWorld2): a heavy set keeps all its zero points,
every other set keeps its non-mixed zero points. -/
noncomputable def refinedPts (w : Fin m) : Finset (Fin n → Bool) :=
  if HeavySet gates p (S w) then zeroPts (S w) else nonMixedPts gates (S w)

theorem mem_refinedPts_zero {w : Fin m} {z : Fin n → Bool} (hz : z ∈ refinedPts S gates p w) :
    ∀ v ∈ S w, z v = false := by
  classical
  unfold refinedPts at hz
  split_ifs at hz
  · exact mem_zeroPts.mp hz
  · exact (mem_nonMixedPts.mp hz).1

/-- `RefinedNoMixedFrac` is `MergeFracOn` on the refined points. -/
theorem refinedNoMixedFrac_iff_mergeFracOn :
    RefinedNoMixedFrac S gates p ↔ MergeFracOn S gates (refinedPts S gates p) := by
  classical
  have hzero : ∀ (w : Fin m) (z : Fin n → Bool), ¬ (∀ v ∈ S w, z v = false) →
      ∃ v ∈ S w, z v = true := by
    intro w z hz
    by_contra hc
    exact hz fun v hv => by
      by_contra hv'
      exact hc ⟨v, hv, by simpa using hv'⟩
  constructor
  · rintro ⟨μ, h0, hS, hM, h1, hl⟩
    refine ⟨μ, h0, fun w z hz => ?_, h1, hl⟩
    unfold refinedPts at hz
    split_ifs at hz with hH
    · exact hS w z (hzero w z fun h => hz (mem_zeroPts.mpr h))
    · rw [mem_nonMixedPts, not_and_or] at hz
      rcases hz with hz | hz
      · exact hS w z (hzero w z hz)
      · exact hM w z hH (not_not.mp hz)
  · rintro ⟨μ, h0, hA, h1, hl⟩
    refine ⟨μ, h0, fun w z ⟨v, hv, hzv⟩ => hA w z fun hz => ?_,
      fun w z hH hmix => hA w z fun hz => ?_, h1, hl⟩
    · rw [mem_refinedPts_zero S gates p hz v hv] at hzv
      exact absurd hzv (by simp)
    · unfold refinedPts at hz
      rw [ite_eq_right hH] at hz
      exact (mem_nonMixedPts.mp hz).2 hmix

variable {S gates p} in
/-- Every set has a refined point (a set that is not heavy has a non-mixed zero point,
`exists_nonMixed_of_not_heavy`). -/
theorem refinedPts_nonempty
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hp : p < gates.length) (hN : (gates[p]'hp).op = GateOp.not)
    (w : Fin m) : (refinedPts S gates p w).Nonempty := by
  classical
  unfold refinedPts
  split_ifs with hH
  · exact zeroPts_nonempty _
  · obtain ⟨z, hz, hmix⟩ := exists_nonMixed_of_not_heavy hg hU hp hN hH
    exact ⟨z, mem_nonMixedPts.mpr ⟨hz, hmix⟩⟩

/-- **RefinedNoMixedPrice**, the price form of `RefinedNoMixedFrac`:
`∀ π ≥ 0, ∑ w, min_{z refined point of w} π(M_z(w)) ≤ π(gates)`. -/
def RefinedNoMixedPrice (hA : ∀ w, (refinedPts S gates p w).Nonempty) : Prop :=
  MergePriceOn S gates (refinedPts S gates p) hA

/-- **LP duality: `RefinedNoMixedFrac ⇔ RefinedNoMixedPrice`.** -/
theorem refinedNoMixedFrac_iff_price (hA : ∀ w, (refinedPts S gates p w).Nonempty) :
    RefinedNoMixedFrac S gates p ↔ RefinedNoMixedPrice S gates p hA :=
  (refinedNoMixedFrac_iff_mergeFracOn S gates p).trans (mergeFracOn_iff_mergePriceOn hA)

end Refined

/-- **RefinedNoMixedPrice on minimal counterexamples closes 951.** -/
theorem no_minCE_of_refinedNoMixedPrice
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hA : ∀ w, (refinedPts S gates p w).Nonempty),
        RefinedNoMixedPrice S gates p hA) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M => by
    obtain ⟨p, hA, hP⟩ := H n m S gates out M
    exact mergeFrac_of_refinedNoMixedFrac S gates p
      ((refinedNoMixedFrac_iff_price S gates p hA).mpr hP)

end PEqualNP.Outside.L_meta_951_aux
