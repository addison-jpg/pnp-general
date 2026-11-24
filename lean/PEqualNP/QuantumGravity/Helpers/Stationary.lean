import PEqualNP.Defs.QuantumGravity
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Probability.ProbabilityMassFunction.Monad
import PEqualNP.QuantumGravity.Helpers.FixedPoint

/-!
Helpers for L-qg-102: every Markov kernel on a nonempty finite type has a stationary distribution.

The proof is linear algebra over `ℝ`. Write `P` for the transition matrix of the kernel `K`,
`P x y = (K x y).toReal`.

1. Every row of `P` sums to `1`, so `P - 1` sends the all-ones vector to `0`, so
   `det (P - 1) = 0`, so some nonzero row vector `v` has `v ᵥ* P = v`
   (`exists_vecMul_fixed`).
2. The row vector `|v|` is also fixed by `P`: `|v| ᵥ* P ≥ |v|` in every entry, by the triangle
   inequality, and both sides have the same sum, because the rows of `P` sum to `1`
   (`vecMul_abs_fixed`).
3. `|v|` is nonnegative and nonzero; divided by its sum, it is a probability mass function that
   `K` carries to itself (`exists_stationary_of_fixed`).

A second proof, `exists_stationary_of_fixedPoint`, runs through the general fixed point theorem
for affine maps (`Helpers/FixedPoint.lean`): the probability vectors on `S` are a nonempty
compact convex set, and `v ↦ v ᵥ* P` is a linear map that carries it into itself. The quantum
form of Deutsch consistency (card D-qg-2) is meant to follow the same pattern.
-/

namespace PEqualNP.QuantumGravity.Helpers

open Matrix

section Stationary

variable {S : Type}

/-- The transition matrix of a Markov kernel: the entry at `x, y` is the probability that `K`
moves `x` to `y`, as a real number. -/
noncomputable def transitionMatrix (K : S → PMF S) : Matrix S S ℝ :=
  fun x y => (K x y).toReal

theorem transitionMatrix_nonneg (K : S → PMF S) (x y : S) : 0 ≤ transitionMatrix K x y :=
  ENNReal.toReal_nonneg

variable [Fintype S]

/-- Every row of the transition matrix sums to `1`. -/
theorem sum_transitionMatrix (K : S → PMF S) (x : S) : ∑ y, transitionMatrix K x y = 1 := by
  have h1 := PMF.tsum_coe (K x)
  rw [tsum_fintype] at h1
  unfold transitionMatrix
  rw [← ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top (K x) y), h1, ENNReal.toReal_one]

/-- Some nonzero real row vector is fixed by the transition matrix. -/
theorem exists_vecMul_fixed [Nonempty S] (K : S → PMF S) :
    ∃ v : S → ℝ, v ≠ 0 ∧ v ᵥ* transitionMatrix K = v := by
  classical
  have hdet : (transitionMatrix K - 1).det = 0 := by
    rw [← exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h (Classical.arbitrary S)
      simp at this
    · rw [sub_mulVec, one_mulVec, sub_eq_zero]
      funext x
      simp [mulVec, dotProduct, sum_transitionMatrix]
  obtain ⟨v, hv, hv0⟩ := exists_vecMul_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  rwa [vecMul_sub, vecMul_one, sub_eq_zero] at hv0

/-- The entrywise absolute value of a row vector fixed by a matrix with nonnegative entries and
rows summing to `1` is also fixed by it. -/
theorem vecMul_abs_fixed {P : Matrix S S ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {v : S → ℝ} (hv : v ᵥ* P = v) :
    (fun x => |v x|) ᵥ* P = fun x => |v x| := by
  set w : S → ℝ := fun x => |v x| with hw
  have hge : ∀ y, w y ≤ (w ᵥ* P) y := by
    intro y
    calc w y = |(v ᵥ* P) y| := by rw [hv]
      _ = |∑ x, v x * P x y| := rfl
      _ ≤ ∑ x, |v x * P x y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, w x * P x y := by simp_rw [abs_mul, abs_of_nonneg (hP _ _), hw]
      _ = (w ᵥ* P) y := rfl
  have hsum : ∑ y, (w ᵥ* P) y = ∑ y, w y := by
    simp only [vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  have hzero : ∀ y ∈ Finset.univ, (w ᵥ* P) y - w y = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.2 (hge y))).1
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  funext y
  exact sub_eq_zero.1 (hzero y (Finset.mem_univ y))

/-- A nonnegative real row vector with positive sum, fixed by the transition matrix of `K`,
gives a probability mass function that `K` carries to itself. -/
theorem exists_stationary_of_fixed (K : S → PMF S) {w : S → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) (hw : w ᵥ* transitionMatrix K = w) :
    ∃ μ : PMF S, μ.bind K = μ := by
  set s := ∑ x, w x with hs
  have hq : ∀ x, 0 ≤ w x / s := fun x => div_nonneg (hw0 x) hpos.le
  have hsum : ∑ x, ENNReal.ofReal (w x / s) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hq x), ← Finset.sum_div, div_self hpos.ne',
      ENNReal.ofReal_one]
  refine ⟨PMF.ofFintype (fun x => ENNReal.ofReal (w x / s)) hsum, ?_⟩
  ext y
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.ofFintype_apply]
  have hK : ∀ x, K x y = ENNReal.ofReal (transitionMatrix K x y) :=
    fun x => (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
  simp_rw [hK, ← ENNReal.ofReal_mul (hq _)]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun x _ => mul_nonneg (hq x) (transitionMatrix_nonneg K x y))]
  congr 1
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  exact congrFun hw y

/-- Every Markov kernel on a nonempty finite type has a stationary distribution. -/
theorem exists_stationary [Nonempty S] (K : S → PMF S) : ∃ μ : PMF S, μ.bind K = μ := by
  obtain ⟨v, hv0, hv⟩ := exists_vecMul_fixed K
  have hw := vecMul_abs_fixed (transitionMatrix_nonneg K) (sum_transitionMatrix K) hv
  refine exists_stationary_of_fixed K (fun x => abs_nonneg (v x)) ?_ hw
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hv0
  exact Finset.sum_pos' (fun y _ => abs_nonneg (v y)) ⟨x, Finset.mem_univ x, abs_pos.2 hx⟩

/-- The probability vectors on `S`: real vectors with nonnegative entries that sum to `1`. -/
def probabilityVectors (S : Type) [Fintype S] : Set (S → ℝ) :=
  {v | (∀ x, 0 ≤ v x) ∧ ∑ x, v x = 1}

theorem convex_probabilityVectors : Convex ℝ (probabilityVectors S) := by
  intro u hu v hv a b ha hb hab
  refine ⟨fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hu.1 x)) (mul_nonneg hb (hv.1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hu.2, hv.2, mul_one, hab]

theorem isCompact_probabilityVectors : IsCompact (probabilityVectors S) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {v : S → ℝ | ∀ x, 0 ≤ v x} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun x => isClosed_le continuous_const (continuous_apply x))
    have h2 : IsClosed {v : S → ℝ | ∑ x, v x = 1} :=
      isClosed_eq (continuous_finsetSum _ (fun x _ => continuous_apply x)) continuous_const
    exact h1.inter h2
  · refine isBounded_iff_forall_norm_le.2 ⟨1, fun v hv =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun x => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hv.1 x), ← hv.2]
    exact Finset.single_le_sum (fun y _ => hv.1 y) (Finset.mem_univ x)

theorem nonempty_probabilityVectors [Nonempty S] : (probabilityVectors S).Nonempty := by
  have hc : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun _ => (Fintype.card S : ℝ)⁻¹, fun _ => by positivity, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]

/-- The transition matrix carries probability vectors to probability vectors. -/
theorem mapsTo_vecMul_probabilityVectors (K : S → PMF S) :
    Set.MapsTo (fun v => v ᵥ* transitionMatrix K) (probabilityVectors S)
      (probabilityVectors S) := by
  intro v hv
  refine ⟨fun y => Finset.sum_nonneg
    (fun x _ => mul_nonneg (hv.1 x) (transitionMatrix_nonneg K x y)), ?_⟩
  simp only [vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_transitionMatrix, mul_one]
  exact hv.2

/-- Every Markov kernel on a nonempty finite type has a stationary distribution: the proof
through the fixed point theorem for affine maps. -/
theorem exists_stationary_of_fixedPoint [Nonempty S] (K : S → PMF S) :
    ∃ μ : PMF S, μ.bind K = μ := by
  obtain ⟨w, hw, hfix⟩ := exists_fixedPoint_affine_of_finiteDimensional
    isCompact_probabilityVectors convex_probabilityVectors nonempty_probabilityVectors
    (transitionMatrix K).vecMulLinear.toAffineMap (mapsTo_vecMul_probabilityVectors K)
  exact exists_stationary_of_fixed K hw.1 (by rw [hw.2]; exact one_pos) hfix

end Stationary

end PEqualNP.QuantumGravity.Helpers
