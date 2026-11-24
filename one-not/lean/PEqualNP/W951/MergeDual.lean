import PEqualNP.W951.MergeWorld

/-! MergeDual: MergeFrac with the distributions restricted to allowed points, and its LP dual.

For allowed point sets `A w` (any finsets of points), `MergeFracOn S gates A` asks for
distributions `μ w` supported on `A w` with every wire load `≤ 1` over the merge sets, and
`MergePriceOn S gates A hA` is the price form `∀ π ≥ 0, ∑ w, min_{z ∈ A w} π(M_z(w)) ≤ π(gates)`.

* `mergeFracOn_iff_mergePriceOn`: LP duality, for every `A` with nonempty `A w`
  (`exists_frac_iff_prices`); `nonempty_of_mergeFracOn` (a feasible `A` has nonempty `A w`);
  `mergeFracOn_mono` (enlarging `A` keeps feasibility).
* `A w = zeroPts (S w)`: `mergeFracOn_zeroPts_iff` (= `MergeFrac`), `mergePriceOn_zeroPts_iff`
  (= `MergePrice`).
* `A w = nonMixedPts gates (S w)` (zero points that are world-0 or world-1, MergeWorld):
  `noMixedFrac_iff_mergeFracOn` (= `NoMixedFrac`), the dual `NoMixedPrice`,
  `noMixedFrac_iff_noMixedPrice`, and `no_minCE_of_noMixedPrice`.
* World split: `worldCost` (price of the merge set in the monotone world of the point: `C0` at
  world-0 points, `C1` at world-1 points), `worldCost_eq`, `noMixedPrice_iff_worlds` (NoMixedPrice
  reads only the merge sets of the two monotone circuits `C0`, `C1`).

So every restriction of the support (no mixed points, one world only, minterms of `h`, ...) has
its price form for free, and a proof of any such price form closes `no_minCE`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

section On

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
  (A : Fin m → Finset (Fin n → Bool))

/-- **MergeFrac on allowed points** `A w`: distributions `μ w` supported on `A w` such that every
wire has load `∑ w, ∑ z, μ w z * [g ∈ M_z(w)] ≤ 1`. -/
def MergeFracOn : Prop :=
  ∃ μ : Fin m → (Fin n → Bool) → ℝ,
    (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, z ∉ A w → μ w z = 0) ∧ (∀ w, ∑ z, μ w z = 1) ∧
    ∀ g : ℕ, ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) ≤ 1

/-- **MergePrice on allowed points**, the dual form of `MergeFracOn`:
`∀ π ≥ 0, ∑ w, min_{z ∈ A w} π(M_z(w)) ≤ π(gates)`. -/
def MergePriceOn (hA : ∀ w, (A w).Nonempty) : Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    ∑ w, (A w).inf' (hA w) (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
      ≤ ∑ g ∈ Finset.Ico n (n + gates.length), π g

variable {S gates A}

/-- A feasible family of allowed sets has every `A w` nonempty. -/
theorem nonempty_of_mergeFracOn (h : MergeFracOn S gates A) (w : Fin m) : (A w).Nonempty := by
  obtain ⟨μ, -, hA, h1, -⟩ := h
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h0 : ∑ z, μ w z = 0 := Finset.sum_eq_zero fun z _ => hA w z (by simp [hne])
  rw [h1 w] at h0
  exact one_ne_zero h0

/-- Enlarging the allowed sets keeps feasibility. -/
theorem mergeFracOn_mono {B : Fin m → Finset (Fin n → Bool)} (hAB : ∀ w, A w ⊆ B w)
    (h : MergeFracOn S gates A) : MergeFracOn S gates B := by
  obtain ⟨μ, h0, hA, h1, hl⟩ := h
  exact ⟨μ, h0, fun w z hz => hA w z fun h => hz (hAB w h), h1, hl⟩

/-- Weak duality. -/
theorem mergePriceOn_of_mergeFracOn (hA : ∀ w, (A w).Nonempty) (hf : MergeFracOn S gates A) :
    MergePriceOn S gates A hA := by
  classical
  obtain ⟨μ, h0, hsupp, h1, hload⟩ := hf
  intro π hπ
  calc ∑ w, (A w).inf' (hA w) (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
      ≤ ∑ w, ∑ z, μ w z * ∑ g ∈ mergeSet gates (S w) z, π g := by
        refine Finset.sum_le_sum fun w _ => ?_
        calc (A w).inf' (hA w) (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
            = ∑ z, μ w z * (A w).inf' (hA w) (fun z => ∑ g ∈ mergeSet gates (S w) z, π g) := by
              rw [← Finset.sum_mul, h1 w, one_mul]
          _ ≤ _ := Finset.sum_le_sum fun z _ => ?_
        by_cases hz : z ∈ A w
        · exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hz) (h0 w z)
        · simp [hsupp w z hz]
    _ = ∑ g ∈ Finset.Ico n (n + gates.length),
          (∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0)) * π g := by
        symm
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [ite_mul, zero_mul]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (mergeSet_subset gates (S w) z), Finset.mul_sum]
    _ ≤ ∑ g ∈ Finset.Ico n (n + gates.length), 1 * π g :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hload g) (hπ g)
    _ = _ := by simp

/-- Strong duality (`exists_frac_iff_prices`). -/
theorem mergeFracOn_of_mergePriceOn (hA : ∀ w, (A w).Nonempty)
    (hp : MergePriceOn S gates A hA) : MergeFracOn S gates A := by
  classical
  set O : Fin m → Finset (Finset (Fin gates.length)) :=
    fun w => (A w).image (mergeIdx gates (S w)) with hOdef
  have hO : ∀ w, (O w).Nonempty := fun w => (hA w).image _
  have hprice : ∀ π' : Fin gates.length → ℝ, (∀ a, 0 ≤ π' a) →
      ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π' a) ≤ ∑ a, π' a := by
    intro π' hπ'
    set π : ℕ → ℝ := fun g => if h : g - n < gates.length then π' ⟨g - n, h⟩ else 0 with hπdef
    have hπ : ∀ g, 0 ≤ π g := by
      intro g
      simp only [hπdef]
      split_ifs
      · exact hπ' _
      · exact le_rfl
    have hπe : ∀ a : Fin gates.length, π (n + a) = π' a := by
      intro a
      simp [hπdef]
    have h := hp π hπ
    rw [sum_Ico_eq_sum_fin] at h
    simp only [hπe] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) h
    simp only [hOdef]
    rw [Finset.inf'_image]
    refine Finset.inf'_congr _ rfl fun z _ => ?_
    simp only [Function.comp_apply, sum_mergeSet, hπe]
  obtain ⟨lam, hlam, hl⟩ := (exists_frac_iff_prices O hO).2 hprice
  have hrep : ∀ w M, M ∈ O w → ∃ z, z ∈ A w ∧ mergeIdx gates (S w) z = M :=
    fun w M h => by simpa [hOdef] using h
  let rep : Fin m → Finset (Fin gates.length) → (Fin n → Bool) := fun w M =>
    if h : M ∈ O w then (hrep w M h).choose else fun _ => false
  have hrep1 : ∀ w M, M ∈ O w → rep w M ∈ A w ∧ mergeIdx gates (S w) (rep w M) = M := by
    intro w M h
    simp only [rep, dite_eq_left h]
    exact (hrep w M h).choose_spec
  refine ⟨fun w z => ∑ M ∈ O w, if rep w M = z then lam w M else 0, ?_, ?_, ?_, ?_⟩
  · intro w z
    refine Finset.sum_nonneg fun M _ => ?_
    split_ifs
    · exact hlam.1 w M
    · exact le_rfl
  · intro w z hz
    refine Finset.sum_eq_zero fun M hM => ?_
    rw [ite_eq_right_iff]
    rintro rfl
    exact absurd (hrep1 w M hM).1 hz
  · intro w
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hlam.2.2 w
  · intro g
    by_cases hgI : g ∈ Finset.Ico n (n + gates.length)
    · have hI := Finset.mem_Ico.1 hgI
      obtain ⟨a, rfl⟩ : ∃ a : Fin gates.length, g = n + (a : ℕ) :=
        ⟨⟨g - n, by omega⟩, by simp; omega⟩
      refine le_of_eq_of_le ?_ (hl a)
      unfold load
      refine Finset.sum_congr rfl fun w _ => ?_
      trans ∑ z, ∑ M ∈ O w, if rep w M = z then
          (if n + (a : ℕ) ∈ mergeSet gates (S w) z then lam w M else 0) else 0
      · refine Finset.sum_congr rfl fun z _ => ?_
        by_cases h : n + (a : ℕ) ∈ mergeSet gates (S w) z <;> simp [h]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun M hM => ?_
      rw [Finset.sum_ite_eq]
      have hiff : a ∈ M ↔ n + (a : ℕ) ∈ mergeSet gates (S w) (rep w M) := by
        rw [← mem_mergeIdx, (hrep1 w M hM).2]
      by_cases h : a ∈ M
      · simp [h, hiff.mp h]
      · have hn : n + (a : ℕ) ∉ mergeSet gates (S w) (rep w M) := fun h' => h (hiff.mpr h')
        simp [h, hn]
    · exact le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun z _ =>
        ite_eq_right fun h => hgI (mergeSet_subset _ _ _ h)) zero_le_one

/-- **LP duality on allowed points: `MergeFracOn ⇔ MergePriceOn`.** -/
theorem mergeFracOn_iff_mergePriceOn (hA : ∀ w, (A w).Nonempty) :
    MergeFracOn S gates A ↔ MergePriceOn S gates A hA :=
  ⟨mergePriceOn_of_mergeFracOn hA, mergeFracOn_of_mergePriceOn hA⟩

end On

/-! ## All zero points: MergeFrac -/

theorem mergeFracOn_zeroPts_iff {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) :
    MergeFracOn S gates (fun w => zeroPts (S w)) ↔ MergeFrac S gates := by
  constructor
  · rintro ⟨μ, h0, hA, h1, hl⟩
    refine ⟨μ, h0, fun w z ⟨v, hv, hzv⟩ => hA w z fun hz => ?_, h1, hl⟩
    rw [mem_zeroPts.mp hz v hv] at hzv
    exact absurd hzv (by simp)
  · rintro ⟨μ, h0, hS, h1, hl⟩
    refine ⟨μ, h0, fun w z hz => hS w z ?_, h1, hl⟩
    by_contra hc
    exact hz (mem_zeroPts.mpr fun v hv => by
      by_contra hv'
      exact hc ⟨v, hv, by simpa using hv'⟩)

theorem mergePriceOn_zeroPts_iff {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) :
    MergePriceOn S gates (fun w => zeroPts (S w)) (fun _ => zeroPts_nonempty _) ↔
      MergePrice S gates :=
  Iff.rfl

/-! ## Non-mixed zero points: NoMixedFrac and its price form -/

open Classical in
/-- The non-mixed zero points of `R` (world-0 or world-1, MergeWorld). -/
noncomputable def nonMixedPts {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) :
    Finset (Fin n → Bool) :=
  (zeroPts R).filter fun z => ¬ Mixed gates R z

theorem mem_nonMixedPts {n : ℕ} {gates : List Gate} {R : Finset (Fin n)} {z : Fin n → Bool} :
    z ∈ nonMixedPts gates R ↔ (∀ v ∈ R, z v = false) ∧ ¬ Mixed gates R z := by
  classical
  simp [nonMixedPts, mem_zeroPts]

theorem noMixedFrac_iff_mergeFracOn {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) :
    NoMixedFrac S gates ↔ MergeFracOn S gates (fun w => nonMixedPts gates (S w)) := by
  constructor
  · rintro ⟨μ, h0, hS, hM, h1, hl⟩
    refine ⟨μ, h0, fun w z hz => ?_, h1, hl⟩
    rw [mem_nonMixedPts, not_and_or] at hz
    rcases hz with hz | hz
    · apply hS w z
      by_contra hc
      exact hz fun v hv => by
        by_contra hv'
        exact hc ⟨v, hv, by simpa using hv'⟩
    · exact hM w z (not_not.mp hz)
  · rintro ⟨μ, h0, hA, h1, hl⟩
    refine ⟨μ, h0, fun w z ⟨v, hv, hzv⟩ => hA w z fun hz => ?_,
      fun w z hz => hA w z fun hz' => (mem_nonMixedPts.mp hz').2 hz, h1, hl⟩
    rw [(mem_nonMixedPts.mp hz).1 v hv] at hzv
    exact absurd hzv (by simp)

/-- **NoMixedPrice**, the dual form of `NoMixedFrac`:
`∀ π ≥ 0, ∑ w, min_{z non-mixed zero point of S w} π(M_z(w)) ≤ π(gates)`. -/
def NoMixedPrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hA : ∀ w, (nonMixedPts gates (S w)).Nonempty) : Prop :=
  MergePriceOn S gates (fun w => nonMixedPts gates (S w)) hA

/-- A `NoMixedFrac` family needs a non-mixed zero point for every set. -/
theorem nonempty_nonMixedPts_of_noMixedFrac {n m : ℕ} {S : Fin m → Finset (Fin n)}
    {gates : List Gate} (h : NoMixedFrac S gates) (w : Fin m) :
    (nonMixedPts gates (S w)).Nonempty :=
  nonempty_of_mergeFracOn ((noMixedFrac_iff_mergeFracOn S gates).mp h) w

/-- **LP duality: `NoMixedFrac ⇔ NoMixedPrice`.** -/
theorem noMixedFrac_iff_noMixedPrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hA : ∀ w, (nonMixedPts gates (S w)).Nonempty) :
    NoMixedFrac S gates ↔ NoMixedPrice S gates hA :=
  (noMixedFrac_iff_mergeFracOn S gates).trans (mergeFracOn_iff_mergePriceOn hA)

/-- **NoMixedPrice on minimal counterexamples closes 951.** -/
theorem no_minCE_of_noMixedPrice
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ hA : ∀ w, (nonMixedPts gates (S w)).Nonempty,
        NoMixedPrice S gates hA) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M => by
    obtain ⟨hA, hp⟩ := H n m S gates out M
    exact mergeFrac_of_noMixedFrac S gates ((noMixedFrac_iff_noMixedPrice S gates hA).mpr hp)

/-! ## The world split of the price form -/

open Classical in
/-- The **world cost** of a point for the set `R` under the price `π`: the price of the merge set
of `R` at `z` in the monotone world of `z` (`C0` at a world-0 point, `C1` otherwise). -/
noncomputable def worldCost {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (π : ℕ → ℝ)
    (z : Fin n → Bool) : ℝ :=
  if World0 gates z then ∑ g ∈ mergeSet (C0 gates) R z, π g
  else ∑ g ∈ mergeSet (C1 gates) R z, π g

/-- At a non-mixed point the world cost is the price of the real merge set. -/
theorem worldCost_eq {n : ℕ} {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) {R : Finset (Fin n)} {z : Fin n → Bool}
    (hz : ¬ Mixed gates R z) (π : ℕ → ℝ) :
    worldCost gates R π z = ∑ g ∈ mergeSet gates R z, π g := by
  classical
  unfold worldCost
  split_ifs with h0
  · rw [mergeSet_C0_of_world0 hg hU R h0]
  · have h1 : World1 gates R z := by
      by_contra h1
      exact hz ⟨h0, h1⟩
    rw [mergeSet_C1_of_world1 hg hU h1]

/-- **NoMixedPrice in the two monotone worlds**: the price form of `NoMixedFrac` reads only the
merge sets of the monotone circuits `C0` (at world-0 points) and `C1` (at world-1 points). -/
theorem noMixedPrice_iff_worlds {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hA : ∀ w, (nonMixedPts gates (S w)).Nonempty) :
    NoMixedPrice S gates hA ↔
      ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
        ∑ w, (nonMixedPts gates (S w)).inf' (hA w) (worldCost gates (S w) π)
          ≤ ∑ g ∈ Finset.Ico n (n + gates.length), π g := by
  unfold NoMixedPrice MergePriceOn
  refine forall_congr' fun π => imp_congr_right fun _ => ?_
  rw [Finset.sum_congr rfl fun w _ => Finset.inf'_congr (hA w) rfl fun z hz =>
    worldCost_eq hg hU (mem_nonMixedPts.mp hz).2 π]

end PEqualNP.Outside.L_meta_951_aux
