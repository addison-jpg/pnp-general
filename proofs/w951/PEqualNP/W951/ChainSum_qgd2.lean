import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import PEqualNP.W951.ChainSum

/-!
# L5 as an instance of the telescoping identity (qg-d2; task board `boards/tasks/telescope-l5-l6.md`)

README items L5 (chain sum, `ChainSum.lean`) and L6 (Cesàro displacement, `proofs/main/PEqualNP/QuantumGravity/
Helpers/FixedPoint.lean` in the main project) are one identity, `telescope`: along any path
`x : ℕ → G` in an additive group, `∑_{i<N} (x (i+1) - x i) = x N - x 0`. The same statement, with L6's
instance and the same averaged forms, is `proofs/main/PEqualNP/QuantumGravity/Helpers/Telescope.lean` in the
main project (two Lake projects, so the statement is stated in each).

* `telescope` (Mathlib's `Finset.sum_range_sub`).
* `chainSum_eq_telescope`: L5 for a decreasing chain of finite sets, from `telescope` with `x i = |F i|`.
* `avg_telescope`, `avg_orderings_telescope`, `sum_shapley`: the average over chains. For a set function
  `F` (e.g. the real-witness count of the cube `x_Q = 1`), the uniform average over all orderings of the
  points of the step sums is `F univ - F ∅`, and regrouped by point: the count is the sum over the points of
  each point's step averaged over all chains (its Shapley value), no chain chosen.
-/

namespace PEqualNP.Outside.L_meta_951_aux.ChainSum

open Finset

section Telescope

variable {G : Type*} [AddCommGroup G]

/-- **The common statement of L5 and L6**: along any path the increments sum to the difference of
the ends. -/
theorem telescope (x : ℕ → G) (N : ℕ) : ∑ i ∈ range N, (x (i + 1) - x i) = x N - x 0 :=
  sum_range_sub x N

end Telescope

/-- **L5 as an instance of `telescope`**: along a decreasing chain the gains sum to `|F 0| - |F N|`. -/
theorem chainSum_eq_telescope {α : Type*} [DecidableEq α] (F : ℕ → Finset α)
    (hF : ∀ i, F (i + 1) ⊆ F i) (N : ℕ) :
    ∑ i ∈ range N, ((F i \ F (i + 1)).card : ℤ) = (F 0).card - (F N).card := by
  have hstep : ∀ i, ((F i \ F (i + 1)).card : ℤ) = -(((F (i + 1)).card : ℤ) - (F i).card) := by
    intro i
    have h := card_sdiff_add_card_eq_card (hF i)
    omega
  simp_rw [hstep, sum_neg_distrib]
  rw [telescope (fun i => ((F i).card : ℤ)) N]
  ring

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

end PEqualNP.Outside.L_meta_951_aux.ChainSum
