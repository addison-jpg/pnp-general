import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
A fixed point theorem for affine maps: a continuous affine map that carries a nonempty compact
convex subset of a real normed space into itself fixes a point of it. This is the one
fixed-point argument behind Deutsch consistency, classical (L-qg-102) and quantum (D-qg-2).

The proof uses Cesàro averages and the extreme value theorem, and no subsequence.

1. Start at `x₀ ∈ C`. The Cesàro average `a n = (n + 1)⁻¹ • ∑ k ≤ n, f^[k] x₀` lies in `C`,
   because `C` is convex (`cesaro_mem`).
2. `f` is affine, so `f (a n) - a n = (n + 1)⁻¹ • (f^[n + 1] x₀ - x₀)` (`cesaro_displacement`).
   `C` is bounded, so this displacement tends to `0`.
3. The continuous function `x ↦ ‖f x - x‖` attains its minimum on the compact set `C` at some `x`.
   The minimum is at most every displacement `‖f (a n) - a n‖`, so it is `0`, and `f x = x`.
-/

namespace PEqualNP.QuantumGravity.Helpers

section FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An affine map carries a weighted sum with weights summing to `1` to the weighted sum of the
images. -/
theorem affineMap_sum_smul (f : E →ᵃ[ℝ] E) {ι : Type*} (t : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hw : ∑ i ∈ t, w i = 1) : f (∑ i ∈ t, w i • z i) = ∑ i ∈ t, w i • f (z i) := by
  have hf : ∀ x, f x = f.linear x + f 0 := fun x => by
    have h := f.linear_apply_vsub x 0
    rw [vsub_eq_sub, vsub_eq_sub, sub_zero] at h
    rw [h, sub_add_cancel]
  rw [hf, map_sum]
  simp_rw [hf (z _), map_smul, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]

/-- The weight `(n + 1)⁻¹`, taken `n + 1` times, sums to `1`. -/
theorem sum_cesaroWeight (n : ℕ) : ∑ _k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

/-- The `n`-th Cesàro average of the orbit of `x₀` under `f`: the mean of
`x₀, f x₀, ..., f^[n] x₀`. -/
noncomputable def cesaro (f : E → E) (x₀ : E) (n : ℕ) : E :=
  ∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • f^[k] x₀

/-- The Cesàro averages of an orbit in a convex set `C` lie in `C`. -/
theorem cesaro_mem {C : Set E} (hconv : Convex ℝ C) {f : E → E} (hmaps : Set.MapsTo f C C)
    {x₀ : E} (hx₀ : x₀ ∈ C) (n : ℕ) : cesaro f x₀ n ∈ C :=
  hconv.sum_mem (fun _ _ => by positivity) (sum_cesaroWeight n)
    (fun k _ => hmaps.iterate k hx₀)

/-- An affine map moves the `n`-th Cesàro average by `(n + 1)⁻¹ • (f^[n + 1] x₀ - x₀)`. -/
theorem cesaro_displacement (f : E →ᵃ[ℝ] E) (x₀ : E) (n : ℕ) :
    f (cesaro f x₀ n) - cesaro f x₀ n = ((n : ℝ) + 1)⁻¹ • (f^[n + 1] x₀ - x₀) := by
  unfold cesaro
  rw [affineMap_sum_smul f _ _ _ (sum_cesaroWeight n), ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  rw [← Finset.smul_sum]
  congr 1
  calc ∑ k ∈ Finset.range (n + 1), (f (f^[k] x₀) - f^[k] x₀)
      = ∑ k ∈ Finset.range (n + 1), (f^[k + 1] x₀ - f^[k] x₀) :=
        Finset.sum_congr rfl (fun k _ => by rw [Function.iterate_succ_apply'])
    _ = f^[n + 1] x₀ - f^[0] x₀ := Finset.sum_range_sub (fun k => f^[k] x₀) (n + 1)
    _ = f^[n + 1] x₀ - x₀ := rfl

/-- **Fixed points of affine maps.** A continuous affine map that carries a nonempty compact
convex subset `C` of a real normed space into itself fixes a point of `C`. -/
theorem exists_fixedPoint_affine {C : Set E} (hC : IsCompact C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (f : E →ᵃ[ℝ] E) (hf : ContinuousOn f C) (hmaps : Set.MapsTo f C C) :
    ∃ x ∈ C, f x = x := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hC.isBounded
  have hsmall : ∀ ε > 0, ∃ n, ‖f (cesaro f x₀ n) - cesaro f x₀ n‖ < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * R / ε)
    refine ⟨n, ?_⟩
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hD : ‖f^[n + 1] x₀ - x₀‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith [hR _ (hmaps.iterate (n + 1) hx₀), hR _ hx₀])
    rw [cesaro_displacement, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]
    calc ((n : ℝ) + 1)⁻¹ * ‖f^[n + 1] x₀ - x₀‖ ≤ ((n : ℝ) + 1)⁻¹ * (2 * R) := by gcongr
      _ < ε := by
        rw [inv_mul_lt_iff₀ hn1]
        have := (div_lt_iff₀ hε).1 hn
        nlinarith
  obtain ⟨x, hxC, hmin⟩ := hC.exists_isMinOn ⟨x₀, hx₀⟩ ((hf.sub continuousOn_id).norm)
  refine ⟨x, hxC, ?_⟩
  by_contra hne
  have hpos : 0 < ‖f x - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := hsmall _ hpos
  have hle : ‖f x - x‖ ≤ ‖f (cesaro f x₀ n) - cesaro f x₀ n‖ :=
    hmin (cesaro_mem hconv hmaps hx₀ n)
  exact absurd hn (not_lt.2 hle)

/-- In finite dimension every affine map is continuous, so an affine map that carries a
nonempty compact convex set into itself fixes a point of it. -/
theorem exists_fixedPoint_affine_of_finiteDimensional [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) (f : E →ᵃ[ℝ] E)
    (hmaps : Set.MapsTo f C C) : ∃ x ∈ C, f x = x :=
  exists_fixedPoint_affine hC hconv hne f f.continuous_of_finiteDimensional.continuousOn hmaps

end FixedPoint

end PEqualNP.QuantumGravity.Helpers
