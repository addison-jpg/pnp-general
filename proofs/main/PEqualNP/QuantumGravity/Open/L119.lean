import PEqualNP.QuantumGravity.Gaps
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Seat C2 of `open-qg`: L-qg-119 reduced to one parametrization statement.

Proved here, from Mathlib only:

* `haar_null_of_image`: for any finite index type `ι`, the image of a differentiable map from a
  real space of dimension `< (card ι)^2 = dim U(ι)` meets the unitary group in a set of measure
  `0` for every left-invariant probability measure. The proof averages over a Cayley chart
  `A ↦ (1 + X)(1 - X)⁻¹`, `X` skew-Hermitian made from a real matrix `A`: by Fubini,
  `μ R · vol(ball) = ∫ vol {A | cayley A * h ∈ R} dμ(h)`, and each slice is the image of a
  differentiable map of lower dimension (the inverse Cayley map `U ↦ (U + 1)⁻¹ (U - 1)` composed
  with the parametrization), hence Lebesgue-null by
  `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
* `haar_null_of_cover`: the same for countably many maps.
* `L119_of_knillParametrization : KnillParametrization → Gap.L119`.

Missing: `KnillParametrization`, the Cartan (KAK) form of two-qubit gates that gives
Knill's count `9k + 3n + 1`. It is not in Mathlib.
-/

namespace PEqualNP.QuantumGravity.Open.L119

open MeasureTheory Module

/-- The image of a differentiable map from a space of smaller dimension is Lebesgue-null. -/
theorem addHaar_image_null_of_finrank_lt {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : finrank ℝ P < finrank ℝ E) {g : P → E} {s : Set P} (hg : DifferentiableOn ℝ g s) :
    μ (g '' s) = 0 := by
  set m := finrank ℝ P
  set d := finrank ℝ E
  let e1 := (Module.finBasis ℝ P).equivFun
  let e2 := (Module.finBasis ℝ E).equivFun
  let π : E →ₗ[ℝ] P :=
    e1.symm.toLinearMap ∘ₗ LinearMap.funLeft ℝ ℝ (Fin.castLE hdim.le) ∘ₗ e2.toLinearMap
  have hπ : Function.Surjective π := by
    have := LinearMap.funLeft_surjective_of_injective (R := ℝ) (M := ℝ) _
      (Fin.castLE_injective hdim.le)
    exact e1.symm.surjective.comp (this.comp e2.surjective)
  obtain ⟨ι, hι⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  have hπι : ∀ p, π (ι p) = p := fun p => LinearMap.congr_fun hι p
  have hιinj : Function.Injective ι := fun a b h => by rw [← hπι a, ← hπι b, h]
  have hrange : LinearMap.range ι ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_of_inj hιinj
    rw [htop, finrank_top] at h1
    omega
  let πc : E →L[ℝ] P := LinearMap.toContinuousLinearMap π
  have hS : (ι '' s : Set E) ⊆ (LinearMap.range ι : Set E) := by
    rintro _ ⟨p, -, rfl⟩; exact ⟨p, rfl⟩
  have hnull : μ (ι '' s) = 0 :=
    measure_mono_null hS (Measure.addHaar_submodule μ _ hrange)
  have hdiff : DifferentiableOn ℝ (g ∘ πc) (ι '' s) := by
    refine hg.comp πc.differentiableOn ?_
    rintro _ ⟨p, hp, rfl⟩
    simpa [πc, hπι] using hp
  have himg : g '' s = (g ∘ πc) '' (ι '' s) := by
    rw [Set.image_image]; congr 1; ext p; simp [πc, hπι]
  rw [himg]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hdiff hnull


section Cayley

open Matrix
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A skew-Hermitian matrix has no eigenvalue `1`. -/
theorem isUnit_det_one_sub {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) : IsUnit (1 - X).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hXv : X *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv.symm
  have hrow : star v ᵥ* X = -star v := by
    have h1 := Matrix.star_mulVec Xᴴ v
    rw [conjTranspose_conjTranspose, hX, neg_mulVec, hXv, star_neg] at h1
    exact h1.symm
  have ha : star v ⬝ᵥ v = -(star v ⬝ᵥ v) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ (X *ᵥ v) := by rw [hXv]
      _ = (star v ᵥ* X) ⬝ᵥ v := (dotProduct_mulVec _ _ _)
      _ = -(star v ⬝ᵥ v) := by rw [hrow, neg_dotProduct]
  have : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := by linear_combination ha
    simpa using h2
  exact hv0 (dotProduct_star_self_eq_zero.1 this)

/-- The Cayley transform `(1 + X) (1 - X)⁻¹`. -/
noncomputable def cayley (X : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 + X) * (1 - X)⁻¹

theorem cayley_mul_one_sub {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) :
    cayley X * (1 - X) = 1 + X := by
  rw [cayley, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_one_sub hX), Matrix.mul_one]

theorem cayley_mem_unitaryGroup {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) :
    cayley X ∈ Matrix.unitaryGroup ι ℂ := by
  have hX' : (-X)ᴴ = -(-X) := by rw [conjTranspose_neg, hX]
  have h1 := isUnit_det_one_sub hX
  have h2 : IsUnit (1 + X).det := by simpa [sub_eq_add_neg] using isUnit_det_one_sub hX'
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, cayley, conjTranspose_mul,
    conjTranspose_nonsing_inv, conjTranspose_add, conjTranspose_sub, conjTranspose_one, hX,
    sub_neg_eq_add, ← sub_eq_add_neg]
  have hcomm : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]; abel
  calc (1 + X)⁻¹ * (1 - X) * ((1 + X) * (1 - X)⁻¹)
      = (1 + X)⁻¹ * ((1 - X) * (1 + X)) * (1 - X)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1 + X)⁻¹ * ((1 + X) * (1 - X)) * (1 - X)⁻¹ := by rw [hcomm]
    _ = ((1 + X)⁻¹ * (1 + X)) * ((1 - X) * (1 - X)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul _ h2, mul_nonsing_inv _ h1, Matrix.one_mul]

/-- The Cayley transform is inverted by `U ↦ (U + 1)⁻¹ (U - 1)`. -/
theorem cayley_inv {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) :
    IsUnit (cayley X + 1) ∧ (cayley X + 1)⁻¹ * (cayley X - 1) = X := by
  have key := cayley_mul_one_sub hX
  set U := cayley X
  have h2 : (U + 1) * (1 - X) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.add_mul, key, Matrix.one_mul, two_smul]; abel
  have hsub : U - 1 = (U + 1) * X := by
    have h := key
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    rw [Matrix.add_mul, Matrix.one_mul, ← sub_eq_zero]
    have : U - 1 - (U * X + X) = (U - U * X) - (1 + X) := by abel
    rw [this, h, sub_self]
  have hunit : IsUnit (U + 1) := by
    have : IsUnit ((U + 1) * ((1 / 2 : ℂ) • (1 - X))) := by
      rw [Matrix.mul_smul, h2, smul_smul]; norm_num
    exact isUnit_of_mul_isUnit_left this
  refine ⟨hunit, ?_⟩
  have hdet : IsUnit (U + 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  rw [hsub, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]

end Cayley


/-- The averaging step: if every right slice `{A | c A * h ∈ R}` is `ν`-null for a nonzero
s-finite `ν`, then `R` is null for every left-invariant probability measure. -/
theorem null_of_slices {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace E]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (hleft : ∀ g : G, Measurable (g * ·)) (ν : Measure E) [SFinite ν] (hν : ν ≠ 0)
    (c : E → G) (R : Set G) (hR : MeasurableSet R)
    (hset : MeasurableSet {p : G × E | c p.2 * p.1 ∈ R})
    (hslice : ∀ h : G, ν {A | c A * h ∈ R} = 0) : μ R = 0 := by
  have h1 : μ.prod ν {p : G × E | c p.2 * p.1 ∈ R} = 0 := by
    rw [Measure.prod_apply hset]
    simp [hslice]
  have h2 : μ.prod ν {p : G × E | c p.2 * p.1 ∈ R} = μ R * ν Set.univ := by
    rw [Measure.prod_apply_symm hset]
    have : ∀ A : E, μ ((fun x => (x, A)) ⁻¹' {p : G × E | c p.2 * p.1 ∈ R}) = μ R := by
      intro A
      change μ ((fun h => c A * h) ⁻¹' R) = μ R
      rw [← Measure.map_apply (hleft (c A)) hR, map_mul_left_eq_self]
    simp only [this, lintegral_const]
  have h3 : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.2 hν
  rw [h1] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_right h3

section Main

set_option linter.unusedSectionVars false

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The skew-Hermitian matrix of a real matrix: antisymmetric part plus `i` times the symmetric
part. Every skew-Hermitian matrix arises once. -/
noncomputable def skewOf (A : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (((A i j - A j i) / 2 : ℝ) : ℂ) + (((A i j + A j i) / 2 : ℝ) : ℂ) * Complex.I

theorem skewOf_conjTranspose (A : ι → ι → ℝ) : (skewOf A)ᴴ = -skewOf A := by
  ext i j
  apply Complex.ext <;> simp [skewOf] <;> ring

/-- A real-linear left inverse of `skewOf`. -/
noncomputable def realOf : Matrix ι ι ℂ →ₗ[ℝ] (ι → ι → ℝ) where
  toFun X i j := (X i j).re + (X i j).im
  map_add' X Y := by ext i j; simp; ring
  map_smul' c X := by ext i j; simp; ring

theorem realOf_skewOf (A : ι → ι → ℝ) : realOf (skewOf A) = A := by
  ext i j; simp [realOf, skewOf]; ring

theorem continuous_skewOf : Continuous (skewOf (ι := ι)) := by
  refine continuous_matrix fun i j => ?_
  simp only [skewOf, of_apply]
  fun_prop

theorem continuous_cayley_skewOf : Continuous fun A : ι → ι → ℝ => cayley (skewOf A) := by
  have hM : Continuous fun A : ι → ι → ℝ => 1 - skewOf A := continuous_const.sub continuous_skewOf
  have hinv : (fun A : ι → ι → ℝ => (1 - skewOf A)⁻¹) =
      fun A => (1 - skewOf A).det⁻¹ • (1 - skewOf A).adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hc : Continuous fun A : ι → ι → ℝ => (1 - skewOf A)⁻¹ := by
    rw [hinv]
    exact (hM.matrix_det.inv₀ fun A => (isUnit_det_one_sub (skewOf_conjTranspose A)).ne_zero).smul
      hM.matrix_adjugate
  exact (continuous_const.add continuous_skewOf).matrix_mul hc

/-- The Cayley chart, as a map into the unitary group. -/
noncomputable def cayleyU (A : ι → ι → ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨cayley (skewOf A), cayley_mem_unitaryGroup (skewOf_conjTranspose A)⟩

theorem continuous_cayleyU : Continuous (cayleyU (ι := ι)) :=
  continuous_cayley_skewOf.subtype_mk _

end Main


section Chart

open Matrix

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- One slice of the averaging step is Lebesgue-null. -/
theorem slice_null {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P < Fintype.card ι * Fintype.card ι)
    (φ : P → Matrix ι ι ℂ) (s : Set P) (hφ : DifferentiableOn ℝ φ s)
    (h : Matrix.unitaryGroup ι ℂ) :
    (volume : Measure (ι → ι → ℝ))
      {A | ((cayleyU A * h : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ∈ φ '' s} = 0 := by
  set ψ : P → Matrix ι ι ℂ := fun p => φ p * star (h : Matrix ι ι ℂ) with hψdef
  set s' := {p | p ∈ s ∧ IsUnit (ψ p + 1)}
  let g : P → (ι → ι → ℝ) := fun p => realOf (Ring.inverse (ψ p + 1) * (ψ p - 1))
  have hsub : {A | ((cayleyU A * h : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) ∈ φ '' s} ⊆
      g '' s' := by
    rintro A ⟨p, hp, hpA⟩
    have hU : cayley (skewOf A) = ψ p := by
      rw [hψdef]
      simp only [hpA, Submonoid.coe_mul, cayleyU]
      rw [Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff.1 h.2), Matrix.mul_one]
    obtain ⟨hunit, hinv⟩ := cayley_inv (skewOf_conjTranspose A)
    rw [hU] at hunit hinv
    refine ⟨p, ⟨hp, hunit⟩, ?_⟩
    simp only [g]
    rw [← Matrix.nonsing_inv_eq_ringInverse, hinv, realOf_skewOf]
  have hg : DifferentiableOn ℝ g s' := by
    have hψ : DifferentiableOn ℝ ψ s' := (hφ.mono (fun p (hp : p ∈ s') => hp.1)).mul_const _
    intro p hp
    have h1 : DifferentiableWithinAt ℝ (fun p => Ring.inverse (ψ p + 1)) s' p :=
      DifferentiableAt.comp_differentiableWithinAt (g := Ring.inverse) p
        (differentiableAt_inverse hp.2) ((hψ p hp).add_const 1)
    have h2 := h1.mul ((hψ p hp).sub_const 1)
    exact (LinearMap.toContinuousLinearMap (realOf (ι := ι))).differentiableAt.comp_differentiableWithinAt
      p h2
  have hfin : finrank ℝ (ι → ι → ℝ) = Fintype.card ι * Fintype.card ι := by
    simp [Module.finrank_pi_fintype]
  exact measure_mono_null hsub
    (addHaar_image_null_of_finrank_lt volume (hfin ▸ hdim) hg)

/-- The image of a differentiable map from a space of dimension below `(card ι)^2`, the real
dimension of the unitary group, is null for every left-invariant probability measure. -/
theorem haar_null_of_image {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    (μ : Measure (Matrix.unitaryGroup ι ℂ)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (hdim : finrank ℝ P < Fintype.card ι * Fintype.card ι) (φ : P → Matrix ι ι ℂ) (s : Set P)
    (hs : IsSigmaCompact s) (hφ : DifferentiableOn ℝ φ s) :
    μ (Subtype.val ⁻¹' (φ '' s)) = 0 := by
  have hR : MeasurableSet (Subtype.val ⁻¹' (φ '' s) : Set (Matrix.unitaryGroup ι ℂ)) := by
    obtain ⟨K, hK, hU⟩ := hs.image_of_continuousOn hφ.continuousOn
    rw [← hU]
    exact measurable_subtype_coe (MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet)
  refine null_of_slices μ (fun g => (continuous_const.mul continuous_id).measurable)
    ((volume : Measure (ι → ι → ℝ)).restrict (Metric.ball 0 1)) ?_ cayleyU _ hR ?_ ?_
  · rw [Ne, Measure.restrict_eq_zero]
    exact (Metric.measure_ball_pos volume 0 one_pos).ne'
  · exact ((continuous_cayleyU.comp continuous_snd).mul continuous_fst).measurable hR
  · intro h
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
      (slice_null hdim φ s hφ h).le)

/-- The same, for a countable family of everywhere differentiable maps from `Fin m → ℝ`, with
values written as arrays `ι → ι → ℂ` (any norm: they are all equivalent). -/
theorem haar_null_of_cover {m : ℕ} (hdim : m < Fintype.card ι * Fintype.card ι)
    (μ : Measure (Matrix.unitaryGroup ι ℂ)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {J : Type} [Countable J] (φ : J → (Fin m → ℝ) → (ι → ι → ℂ))
    (hφ : ∀ j, Differentiable ℝ (φ j)) (R : Set (Matrix.unitaryGroup ι ℂ))
    (hR : ∀ U ∈ R, ∃ j p, φ j p = (U : Matrix ι ι ℂ)) : μ R = 0 := by
  let e : (ι → ι → ℂ) →L[ℝ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hsub : R ⊆ ⋃ j, Subtype.val ⁻¹' ((fun p => e (φ j p)) '' Set.univ) := by
    intro U hU
    obtain ⟨j, p, hp⟩ := hR U hU
    exact Set.mem_iUnion.2 ⟨j, p, Set.mem_univ _, hp⟩
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  refine haar_null_of_image μ (by simpa using hdim) _ _ isSigmaCompact_univ ?_
  exact (e.differentiable.comp (hφ j)).differentiableOn

end Chart

/-! ### L-qg-119 from Knill's parametrization -/

/-- The parametrization behind Knill's Theorem 3.4 (1995): the products of at most `k`
two-qubit gates on `n` qubits are covered by countably many everywhere differentiable maps from
`ℝ^(9k + 3n + 1)`. It comes from the Cartan (KAK) decomposition of a two-qubit gate,
`(A ⊗ B) exp(i(a XX + b YY + c ZZ)) (A' ⊗ B')`, with the single-qubit factors pushed into the
next layer and written by Euler angles; the countable index records the qubit pairs of the
gates. The KAK decomposition of `U(4)` is not in Mathlib. -/
def KnillParametrization : Prop :=
  ∀ n k : ℕ, ∃ (J : Type) (_ : Countable J)
    (φ : J → (Fin (9 * k + 3 * n + 1) → ℝ) → (Qubits n → Qubits n → ℂ)),
    (∀ j, Differentiable ℝ (φ j)) ∧
      ∀ U ∈ ReachableIn (twoQubitGates n) k, ∃ j p, φ j p = (U : Matrix (Qubits n) (Qubits n) ℂ)

/-- L-qg-119 follows from Knill's parametrization: the measure-theoretic half of the dimension
count (a lower-dimensional differentiable image is Haar-null) is proved here. -/
theorem L119_of_knillParametrization (h : KnillParametrization) : Gap.L119 := by
  intro n k μ _ _ hlt
  obtain ⟨J, _, φ, hφ, hcov⟩ := h n k
  refine haar_null_of_cover ?_ μ φ hφ _ hcov
  have : Fintype.card (Qubits n) * Fintype.card (Qubits n) = 4 ^ n := by
    simp [Qubits, ← mul_pow]
  rw [this]; exact hlt

end PEqualNP.QuantumGravity.Open.L119
