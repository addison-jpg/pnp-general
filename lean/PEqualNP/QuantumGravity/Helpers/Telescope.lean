import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.Perm
import PEqualNP.QuantumGravity.Helpers.FixedPoint

/-!
# The common identity of README items L5 and L6 (task board `boards/tasks/telescope-l5-l6.md`)

L5 (the chain sum, `one-not/lean/PEqualNP/W951/ChainSum.lean`) and L6 (the Cesàro displacement of a
closed timelike curve, `Helpers/FixedPoint.lean`) are both the telescoping identity: along any path
`x : ℕ → G` in an additive group, the increments sum to the difference of the ends.

* `telescope`: `∑_{i<N} (x (i+1) - x i) = x N - x 0` (Mathlib's `Finset.sum_range_sub`).
* `cesaro_displacement_eq_telescope`: L6 is `(n+1)⁻¹` times the telescoped orbit `k ↦ f^[k] x₀`.
* `avg_telescope`: a weighted average (weights summing to `1`) of paths with common end points
  telescopes to the same difference: the average step sum does not depend on the weights.
* `avg_orderings_telescope`: the uniform average over ALL orderings `σ` of the points of `Fin n`,
  the path being the prefix sets `pre σ i`, gives `F univ - F ∅` for any set function `F`.
* `sum_shapley`: regrouped by point, `∑_v shapley F v = F univ - F ∅`, where `shapley F v` is the
  average over orderings of the step at which `v` enters (its Shapley value).

For the circuit count (L5) with `F Q` the real-witness count of the cube `x_Q = 1`, the last line
says: the count is the sum over the POINTS of each point's step averaged over all chains, with no
chain chosen. For L6 the average is over time. The map time ↔ chain of cubes is a PREMISE.
-/

namespace PEqualNP.QuantumGravity.Helpers.Telescope

open Finset

section Telescope

variable {G : Type*} [AddCommGroup G]

/-- **The common statement of L5 and L6**: along any path the increments sum to the difference of
the ends. -/
theorem telescope (x : ℕ → G) (N : ℕ) : ∑ i ∈ range N, (x (i + 1) - x i) = x N - x 0 :=
  sum_range_sub x N

end Telescope

section Cesaro

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **L6 as an instance of `telescope`**: the displacement of the `n`-th Cesàro average is
`(n + 1)⁻¹` times the sum of the steps of the orbit. -/
theorem cesaro_displacement_eq_telescope (f : E →ᵃ[ℝ] E) (x₀ : E) (n : ℕ) :
    f (cesaro f x₀ n) - cesaro f x₀ n =
      ((n : ℝ) + 1)⁻¹ • ∑ k ∈ range (n + 1), (f^[k + 1] x₀ - f^[k] x₀) := by
  rw [cesaro_displacement, telescope (fun k => f^[k] x₀)]
  rfl

end Cesaro

section Average

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Averaged form**: a weighted average of paths with common end points `A`, `B` telescopes to
`B - A`, whatever the weights (summing to `1`). -/
theorem avg_telescope {ι : Type*} (c : Finset ι) (w : ι → ℝ) (hw : ∑ j ∈ c, w j = 1)
    (x : ι → ℕ → E) (N : ℕ) (A B : E) (h0 : ∀ j ∈ c, x j 0 = A) (hN : ∀ j ∈ c, x j N = B) :
    ∑ j ∈ c, w j • ∑ i ∈ range N, (x j (i + 1) - x j i) = B - A := by
  calc ∑ j ∈ c, w j • ∑ i ∈ range N, (x j (i + 1) - x j i)
      = ∑ j ∈ c, w j • (B - A) :=
        sum_congr rfl fun j hj => by rw [telescope, hN j hj, h0 j hj]
    _ = (∑ j ∈ c, w j) • (B - A) := (sum_smul ..).symm
    _ = B - A := by rw [hw, one_smul]

variable {n : ℕ}

/-- The first `i` points in the ordering `σ`: `{σ 0, …, σ (i - 1)}`. -/
def pre (σ : Equiv.Perm (Fin n)) (i : ℕ) : Finset (Fin n) :=
  (univ.filter fun k : Fin n => (k : ℕ) < i).map σ.toEmbedding

theorem pre_zero (σ : Equiv.Perm (Fin n)) : pre σ 0 = ∅ := by
  simp [pre]

theorem pre_n (σ : Equiv.Perm (Fin n)) : pre σ n = univ := by
  have h : (univ.filter fun k : Fin n => (k : ℕ) < n) = univ :=
    filter_true_of_mem fun k _ => k.isLt
  rw [pre, h]
  exact map_univ_equiv σ

/-- **Average over all orderings**: for any set function `F`, the uniform average over all
orderings of `Fin n` of the step sums along the prefix chains is `F univ - F ∅`. -/
theorem avg_orderings_telescope (F : Finset (Fin n) → E) :
    ∑ σ : Equiv.Perm (Fin n), ((n.factorial : ℝ)⁻¹) •
      ∑ i ∈ range n, (F (pre σ (i + 1)) - F (pre σ i)) = F univ - F ∅ := by
  refine avg_telescope univ (fun _ => ((n.factorial : ℝ)⁻¹)) ?_ (fun σ i => F (pre σ i)) n
    (F ∅) (F univ) (fun σ _ => by rw [pre_zero]) (fun σ _ => by rw [pre_n])
  rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- The step at which the point `v` enters along the ordering `σ`. -/
def stepAt (F : Finset (Fin n) → E) (σ : Equiv.Perm (Fin n)) (v : Fin n) : E :=
  F (pre σ ((σ.symm v : ℕ) + 1)) - F (pre σ (σ.symm v))

/-- **Shapley value** of the point `v`: its entering step averaged over all orderings. -/
noncomputable def shapley (F : Finset (Fin n) → E) (v : Fin n) : E :=
  ∑ σ : Equiv.Perm (Fin n), ((n.factorial : ℝ)⁻¹) • stepAt F σ v

omit [Module ℝ E] in
/-- Along one ordering, the step sum regrouped by the point that enters. -/
theorem sum_stepAt (F : Finset (Fin n) → E) (σ : Equiv.Perm (Fin n)) :
    ∑ v : Fin n, stepAt F σ v = ∑ i ∈ range n, (F (pre σ (i + 1)) - F (pre σ i)) := by
  have h := Equiv.sum_comp σ.symm (fun i : Fin n => F (pre σ ((i : ℕ) + 1)) - F (pre σ i))
  simp only [stepAt]
  rw [h]
  exact Fin.sum_univ_eq_sum_range (fun i => F (pre σ (i + 1)) - F (pre σ i)) n

/-- **Efficiency**: the Shapley values of the points add up to `F univ - F ∅`. For the circuit
count this is the count as a sum over points of each point's chain-averaged step. -/
theorem sum_shapley (F : Finset (Fin n) → E) : ∑ v : Fin n, shapley F v = F univ - F ∅ := by
  unfold shapley
  rw [sum_comm, ← avg_orderings_telescope F]
  refine sum_congr rfl fun σ _ => ?_
  rw [← smul_sum, sum_stepAt]

end Average

end PEqualNP.QuantumGravity.Helpers.Telescope
