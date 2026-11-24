import PEqualNP.QuantumGravity.Helpers.Channels
import PEqualNP.QuantumGravity.Helpers.FixedPoint
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Instances.Matrix

/-!
Helpers for L-qg-120: Deutsch's consistency condition for a quantum register. The density matrices on
`Fin d` form a nonempty, compact, convex subset of the finite-dimensional real vector space of complex
`d × d` matrices, and a channel in Kraus form is a real-linear map that sends this set into itself
(L-qg-122). The fixed-point lemma of `Helpers/FixedPoint.lean` (Cesàro averages and compactness, the
lemma L-qg-102 rests on) then gives a fixed density matrix.
-/

namespace PEqualNP.QuantumGravity.Helpers

open Matrix
open scoped ComplexOrder

section ChannelFixedPoint

variable {d : ℕ}

/-- The quadratic form of a positive semidefinite matrix on `a • e_i + b • e_j`. -/
theorem posSemidef_two_point {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (i j : Fin d)
    (a b : ℂ) :
    0 ≤ star a * A i i * a + star a * A i j * b + star b * A j i * a + star b * A j j * b := by
  have h := hA.dotProduct_mulVec_nonneg (Pi.single i a + Pi.single j b)
  simp only [star_add, Pi.star_single, add_dotProduct, mulVec_add, dotProduct_add,
    single_dotProduct, mulVec_single] at h
  simp only [Pi.smul_apply, op_smul_eq_mul, col_apply] at h
  convert h using 1
  ring

/-- On the diagonal of a density matrix stand real numbers in `[0, 1]`. -/
theorem diag_re_le_one {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (i : Fin d) :
    0 ≤ (ρ i i).re ∧ (ρ i i).re ≤ 1 := by
  refine ⟨(diag_of_isDensityMatrix hρ i).1, ?_⟩
  rw [← sum_diag_re_of_isDensityMatrix hρ]
  exact Finset.single_le_sum (f := fun y => (ρ y y).re)
    (fun y _ => (diag_of_isDensityMatrix hρ y).1) (Finset.mem_univ i)

/-- Every entry of a density matrix has norm at most `2`. -/
theorem norm_apply_le_two {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (i j : Fin d) :
    ‖ρ i j‖ ≤ 2 := by
  by_cases hij : i = j
  · subst hij
    rw [(diag_of_isDensityMatrix hρ i).2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (diag_re_le_one hρ i).1]
    linarith [(diag_re_le_one hρ i).2]
  have hH : ρ j i = star (ρ i j) := by
    have := hρ.1.1.apply i j
    rw [← this, star_star]
  have hi := diag_of_isDensityMatrix hρ i; have hj := diag_of_isDensityMatrix hρ j
  have key : ∀ b : ℂ, star b * b = 1 →
      0 ≤ (ρ i i).re + (ρ j j).re + 2 * (b * ρ i j).re := by
    intro b hb
    have h := Complex.nonneg_iff.mp (posSemidef_two_point hρ.1 i j 1 b)
    have e : star b * ρ j j * b = ρ j j := by
      rw [mul_comm (star b * ρ j j) b, ← mul_assoc, mul_comm b (star b), hb, one_mul]
    rw [e, hH] at h
    have h1 := h.1
    simp only [star_one, one_mul, mul_one, Complex.add_re] at h1
    have h2 : (star b * star (ρ i j)).re = (b * ρ i j).re := by
      rw [← star_mul', mul_comm]; exact Complex.conj_re _
    rw [mul_comm (ρ i j) b, h2] at h1
    linarith
  have hre1 := key 1 (by simp); have hre2 := key (-1) (by simp)
  have him1 := key Complex.I (by simp)
  have him2 := key (-Complex.I) (by simp)
  simp only [one_mul, neg_mul, one_mul, Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg] at hre1 hre2 him1 him2
  have hdi := diag_re_le_one hρ i; have hdj := diag_re_le_one hρ j
  have hr : |(ρ i j).re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |(ρ i j).im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc ‖ρ i j‖ ≤ |(ρ i j).re| + |(ρ i j).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 := by linarith

/-- The density matrices are a convex set over `ℝ`. -/
theorem convex_isDensityMatrix : Convex ℝ {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ} := by
  intro x hx y hy a b ha hb hab
  have hsa : (a • x) = ((a : ℂ) • x) := by rw [← algebraMap_smul ℂ a x]; rfl
  have hsb : (b • y) = ((b : ℂ) • y) := by rw [← algebraMap_smul ℂ b y]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsa, hsb]
    exact (hx.1.smul (Complex.zero_le_real.mpr ha)).add (hy.1.smul (Complex.zero_le_real.mpr hb))
  · rw [hsa, hsb, trace_add, trace_smul, trace_smul, hx.2, hy.2, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one, ← Complex.ofReal_add, hab, Complex.ofReal_one]

/-- A channel in Kraus form as a real-linear map. -/
def krausLinear {ι : Type} [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ where
  toFun := krausMap K
  map_add' x y := by
    simp only [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isCompact_isDensityMatrix :
    IsCompact {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ} := by
  have : ProperSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.proper_real _
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {ρ : Matrix (Fin d) (Fin d) ℂ | ρ.PosSemidef} := isClosed_setOfPred_posSemidef
    have h2 : IsClosed {ρ : Matrix (Fin d) (Fin d) ℂ | ρ.trace = 1} :=
      isClosed_eq continuous_id.matrix_trace continuous_const
    exact h1.inter h2
  · refine (Metric.isBounded_closedBall (x := (0 : Matrix (Fin d) (Fin d) ℂ)) (r := 2)).subset ?_
    intro ρ hρ
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.norm_le_iff (by norm_num)).mpr fun i j => norm_apply_le_two hρ i j

/-- Deutsch's consistency condition for a quantum register: every channel in Kraus form on a
nonempty register has a fixed density matrix. -/
theorem exists_fixed_densityMatrix (hd : 0 < d) {ι : Type} [Fintype ι]
    {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K) :
    ∃ ρ, IsDensityMatrix ρ ∧ krausMap K ρ = ρ := by
  obtain ⟨ρ, hρ, hfix⟩ := exists_fixedPoint_affine_of_finiteDimensional
    (isCompact_isDensityMatrix (d := d)) convex_isDensityMatrix
    ⟨_, isDensityMatrix_maximallyMixed hd⟩ (krausLinear K).toAffineMap
    (fun ρ hρ => isDensityMatrix_krausMap hK hρ)
  exact ⟨ρ, hρ, hfix⟩

end ChannelFixedPoint

end PEqualNP.QuantumGravity.Helpers
