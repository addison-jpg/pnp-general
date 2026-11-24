import PEqualNP.W951.CrossWorld

/-!
# PriceOff: MergePrice with prices switched off on a set of wires

Coord assignment (reset). The reduction skeleton for front's candidate lemma (scaffold: on all
cross-world circuits, some optimal dual price vanishes on the cross-world set `X`).

* `priceGap S gates π = ∑_w min_z π(M_z(w)) - π(gates)`; `MergePrice` is `priceGap π ≤ 0` for every
  `π ≥ 0` (`mergePrice_iff_priceGap`).
* `MergePriceOff S gates X`: `priceGap π ≤ 0` for every `π ≥ 0` that vanishes on `X`.
* `ShiftOff S gates X`: every `π ≥ 0` has a `π' ≥ 0` vanishing on `X` with `priceGap π ≤ priceGap π'`.
* `mergePrice_of_off`: `MergePriceOff X ∧ ShiftOff X → MergePrice`; `no_minCE_of_off` closes 951 from
  both on minimal counterexamples. Specializations to the cross-world set `crossSet` (any
  cross-world gate) and `crossSetStrict` (cross-world with hypotheses (i), (ii) of `CrossWorld`; its
  gates are N-dependent, `crossSetStrict_ndep`).
* The easy part: a wire that lies in merge sets of at most one set (`SingleOwner`, which includes
  the wires in no merge set at all) can always be priced `0`: `priceGap_le_zeroOut`,
  `shiftOff_of_singleOwner`, and `mergePriceOff_of_union` (`MergePriceOff (X ∪ Y) → MergePriceOff X`
  for single-owner `Y`). For `X = crossSet` this part is empty: a cross-world gate lies in merge sets
  of two different sets (`crossSet_not_singleOwner`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section Defs

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)

/-- `gap(π) = ∑_w min_z π(M_z(w)) - π(gates)`. -/
noncomputable def priceGap (π : ℕ → ℝ) : ℝ :=
  ∑ w, (zeroPts (S w)).inf' (zeroPts_nonempty _) (fun z => ∑ g ∈ mergeSet gates (S w) z, π g) -
    ∑ g ∈ Finset.Ico n (n + gates.length), π g

/-- `MergePrice` for the prices that vanish on `X`. -/
def MergePriceOff (X : Set ℕ) : Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) → (∀ g ∈ X, π g = 0) → priceGap S gates π ≤ 0

/-- Every price can be moved off `X` without lowering the gap. -/
def ShiftOff (X : Set ℕ) : Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    ∃ π' : ℕ → ℝ, (∀ g, 0 ≤ π' g) ∧ (∀ g ∈ X, π' g = 0) ∧ priceGap S gates π ≤ priceGap S gates π'

theorem mergePrice_iff_priceGap :
    MergePrice S gates ↔ ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) → priceGap S gates π ≤ 0 := by
  unfold MergePrice priceGap
  exact forall₂_congr fun _ _ => sub_nonpos.symm

/-- **The reduction**: `MergePriceOff X` and `ShiftOff X` give `MergePrice`. -/
theorem mergePrice_of_off {X : Set ℕ} (hoff : MergePriceOff S gates X)
    (hshift : ShiftOff S gates X) : MergePrice S gates := by
  rw [mergePrice_iff_priceGap]
  intro π hπ
  obtain ⟨π', hπ', hX, hle⟩ := hshift π hπ
  exact hle.trans (hoff π' hπ' hX)

/-- `MergePriceOff` is antitone in `X`. -/
theorem MergePriceOff.mono {X Y : Set ℕ} (h : MergePriceOff S gates X) (hXY : X ⊆ Y) :
    MergePriceOff S gates Y :=
  fun π hπ hY => h π hπ fun g hg => hY g (hXY hg)

/-- The cross-world gates. -/
def crossSet : Set ℕ := {g | CrossWorld S gates g}

/-- The cross-world gates with hypotheses (i) and (ii) of `CrossWorld` (N-dependent ones). -/
def crossSetStrict : Set ℕ :=
  {g | ∃ a b z z', CrossWorldAt S gates g a b z z' ∧ (∀ v ∈ S a, z' v = false) ∧
    val (C0 gates) (Zof (S a)) g = false}

theorem crossSetStrict_subset : crossSetStrict S gates ⊆ crossSet S gates :=
  fun _ ⟨a, b, z, z', h, _⟩ => ⟨a, b, z, z', h⟩

/-- Every gate of `crossSetStrict` is N-dependent (S1(g) for merge sets). -/
theorem crossSetStrict_ndep (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) : ∀ g ∈ crossSetStrict S gates, NDep n gates g :=
  fun _ ⟨_, _, _, _, h, hi, hii⟩ => h.ndep S hS hg hU hi hii

/-- The reduction for the cross-world set. -/
theorem mergePrice_of_crossOff (hoff : MergePriceOff S gates (crossSet S gates))
    (hshift : ShiftOff S gates (crossSet S gates)) : MergePrice S gates :=
  mergePrice_of_off S gates hoff hshift

end Defs

/-- **951 from the reduction**: if every minimal counterexample has a set `X` with
`MergePriceOff X` and `ShiftOff X`, there is no minimal counterexample. -/
theorem no_minCE_of_off
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ X : Set ℕ, MergePriceOff S gates X ∧ ShiftOff S gates X) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergePrice fun n m S gates out M => by
    obtain ⟨X, hoff, hshift⟩ := H n m S gates out M
    exact mergePrice_of_off S gates hoff hshift

/-! ## The easy part: single-owner wires are free -/

section Single

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)

/-- Merge wires are gate wires. -/
theorem mergeSet_subset_Ico (R : Finset (Fin n)) (z : Fin n → Bool) :
    mergeSet gates R z ⊆ Finset.Ico n (n + gates.length) := by
  intro i hi
  unfold mergeSet at hi
  obtain ⟨j, hj, rfl, -⟩ := (runMT_mem z (upPt z) R gates _ _).mp hi
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

/-- Every wire of `Y` lies in merge sets of at most one set (possibly of none). -/
def SingleOwner (Y : Set ℕ) : Prop :=
  ∀ g ∈ Y, ∀ (w w' : Fin m) (z z' : Fin n → Bool),
    g ∈ mergeSet gates (S w) z → g ∈ mergeSet gates (S w') z' → w = w'

open Classical in
/-- The price `π` with every wire of `Y` set to `0`. -/
noncomputable def zeroOut (Y : Set ℕ) (π : ℕ → ℝ) : ℕ → ℝ :=
  fun g => if g ∈ Y then 0 else π g

theorem zeroOut_nonneg (Y : Set ℕ) {π : ℕ → ℝ} (hπ : ∀ g, 0 ≤ π g) (g : ℕ) :
    0 ≤ zeroOut Y π g := by
  unfold zeroOut; split_ifs <;> simp [hπ g]

theorem zeroOut_mem (Y : Set ℕ) (π : ℕ → ℝ) {g : ℕ} (hg : g ∈ Y) : zeroOut Y π g = 0 := by
  simp [zeroOut, hg]

theorem zeroOut_of_zero (Y : Set ℕ) {π : ℕ → ℝ} {g : ℕ} (hg : π g = 0) : zeroOut Y π g = 0 := by
  unfold zeroOut; split_ifs <;> simp [hg]

/-- **Single-owner wires are free**: zeroing their prices does not lower the gap. -/
theorem priceGap_le_zeroOut {Y : Set ℕ} (hY : SingleOwner S gates Y) {π : ℕ → ℝ}
    (hπ : ∀ g, 0 ≤ π g) : priceGap S gates π ≤ priceGap S gates (zeroOut Y π) := by
  classical
  set G := Finset.Ico n (n + gates.length) with hG
  -- the wires of `Y` owned by `w`
  let Yw : Fin m → Finset ℕ := fun w =>
    G.filter fun g => g ∈ Y ∧ ∃ z, g ∈ mergeSet gates (S w) z
  let A : (ℕ → ℝ) → Fin m → ℝ := fun ρ w =>
    (zeroPts (S w)).inf' (zeroPts_nonempty _) (fun z => ∑ g ∈ mergeSet gates (S w) z, ρ g)
  -- per set: the minimum drops by at most the price of the owned wires
  have hA : ∀ w, A π w - ∑ g ∈ Yw w, π g ≤ A (zeroOut Y π) w := by
    intro w
    refine Finset.le_inf' _ _ fun z hz => ?_
    have h1 : A π w ≤ ∑ g ∈ mergeSet gates (S w) z, π g := Finset.inf'_le _ hz
    have h2 : ∑ g ∈ mergeSet gates (S w) z, π g =
        ∑ g ∈ mergeSet gates (S w) z, zeroOut Y π g +
          ∑ g ∈ (mergeSet gates (S w) z).filter (· ∈ Y), π g := by
      rw [← Finset.sum_filter_add_sum_filter_not (mergeSet gates (S w) z) (· ∈ Y)]
      have e1 : ∑ g ∈ mergeSet gates (S w) z, zeroOut Y π g =
          ∑ g ∈ (mergeSet gates (S w) z).filter (fun g => ¬ g ∈ Y), π g := by
        rw [← Finset.sum_filter_add_sum_filter_not (mergeSet gates (S w) z) (· ∈ Y)]
        have : ∑ g ∈ (mergeSet gates (S w) z).filter (· ∈ Y), zeroOut Y π g = 0 :=
          Finset.sum_eq_zero fun g hg => zeroOut_mem Y π (Finset.mem_filter.mp hg).2
        rw [this, zero_add]
        exact Finset.sum_congr rfl fun g hg => by
          simp [zeroOut, (Finset.mem_filter.mp hg).2]
      rw [e1]
      ring
    have h3 : ∑ g ∈ (mergeSet gates (S w) z).filter (· ∈ Y), π g ≤ ∑ g ∈ Yw w, π g := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g _ _ => hπ g
      intro g hg
      obtain ⟨hgm, hgY⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨mergeSet_subset_Ico gates (S w) z hgm, hgY, z, hgm⟩
    linarith
  -- the owned sets are pairwise disjoint and inside `G ∩ Y`
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (Yw a) (Yw b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro g ha hb
    obtain ⟨-, hgY, za, hza⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, -, zb, hzb⟩ := Finset.mem_filter.mp hb
    exact hab (hY g hgY a b za zb hza hzb)
  have hown : ∑ w, ∑ g ∈ Yw w, π g ≤ ∑ g ∈ G.filter (· ∈ Y), π g := by
    rw [← Finset.sum_biUnion hdisj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g _ _ => hπ g
    intro g hg
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hgG, hgY, -⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hgG, hgY⟩
  -- the total price drops by exactly the price of `G ∩ Y`
  have htot : ∑ g ∈ G, zeroOut Y π g = ∑ g ∈ G, π g - ∑ g ∈ G.filter (· ∈ Y), π g := by
    have s1 := Finset.sum_filter_add_sum_filter_not G (· ∈ Y) π
    have s2 := Finset.sum_filter_add_sum_filter_not G (· ∈ Y) (zeroOut Y π)
    have z1 : ∑ g ∈ G.filter (· ∈ Y), zeroOut Y π g = 0 :=
      Finset.sum_eq_zero fun g hg => zeroOut_mem Y π (Finset.mem_filter.mp hg).2
    have e : ∑ g ∈ G.filter (fun g => ¬ g ∈ Y), zeroOut Y π g =
        ∑ g ∈ G.filter (fun g => ¬ g ∈ Y), π g :=
      Finset.sum_congr rfl fun g hg => by simp [zeroOut, (Finset.mem_filter.mp hg).2]
    linarith
  have hsum : ∑ w, A π w - ∑ w, ∑ g ∈ Yw w, π g ≤ ∑ w, A (zeroOut Y π) w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun w _ => hA w
  unfold priceGap
  rw [← hG, htot]
  change ∑ w, A π w - ∑ g ∈ G, π g ≤ ∑ w, A (zeroOut Y π) w - (∑ g ∈ G, π g -
    ∑ g ∈ G.filter (· ∈ Y), π g)
  linarith

/-- **ShiftOff for single-owner wires** (including the wires in no merge set). -/
theorem shiftOff_of_singleOwner {Y : Set ℕ} (hY : SingleOwner S gates Y) :
    ShiftOff S gates Y :=
  fun π hπ => ⟨zeroOut Y π, zeroOut_nonneg Y hπ, fun _ hg => zeroOut_mem Y π hg,
    priceGap_le_zeroOut S gates hY hπ⟩

/-- Single-owner wires can be added to `X` for free:
`MergePriceOff (X ∪ Y) → MergePriceOff X`. -/
theorem mergePriceOff_of_union {X Y : Set ℕ} (hY : SingleOwner S gates Y)
    (h : MergePriceOff S gates (X ∪ Y)) : MergePriceOff S gates X := by
  intro π hπ hX
  refine (priceGap_le_zeroOut S gates hY hπ).trans (h _ (zeroOut_nonneg Y hπ) ?_)
  rintro g (hg | hg)
  · exact zeroOut_of_zero Y (hX g hg)
  · exact zeroOut_mem Y π hg

/-- `ShiftOff X` and single-owner `Y` give `ShiftOff (X ∪ Y)`. -/
theorem ShiftOff.union_singleOwner {X Y : Set ℕ} (h : ShiftOff S gates X)
    (hY : SingleOwner S gates Y) : ShiftOff S gates (X ∪ Y) := by
  intro π hπ
  obtain ⟨π', hπ', hX, hle⟩ := h π hπ
  refine ⟨zeroOut Y π', zeroOut_nonneg Y hπ', ?_,
    hle.trans (priceGap_le_zeroOut S gates hY hπ')⟩
  rintro g (hg | hg)
  · exact zeroOut_of_zero Y (hX g hg)
  · exact zeroOut_mem Y π' hg

/-- For the cross-world set the easy part is empty: a cross-world gate lies in merge sets of two
different sets, so no subset of `crossSet` with a gate in it is single-owner. -/
theorem crossSet_not_singleOwner {Y : Set ℕ} (hY : SingleOwner S gates Y) :
    ∀ g ∈ Y, g ∉ crossSet S gates := by
  rintro g hgY ⟨a, b, z, z', hab, ⟨-, -, ha⟩, ⟨-, -, hb⟩⟩
  exact hab (hY g hgY a b z z' ha hb)

end Single

end PEqualNP.Outside.L_meta_951_aux
