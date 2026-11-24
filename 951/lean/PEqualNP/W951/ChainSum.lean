import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The chain sum (README item L5)

A decreasing chain of finite sets `F 0 ⊇ F 1 ⊇ … ⊇ F N` is summed by its steps: the size of `F 0`
is the size of `F N` plus the sum of the sizes of the differences. With `F i` the real-witness
gates of the cube after `i` points are set to `1`, the differences are the gains, and the count
`base ≤ |F 0|` is the statement that the sum of `gain - cost` along the chain is nonnegative.
The point step asks every term to be nonnegative; the count asks only the sum.
-/

namespace PEqualNP.Outside.L_meta_951_aux.ChainSum

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Chain sum**: `|F 0| = |F N| + ∑ i < N, |F i \ F (i + 1)|` for a decreasing chain. -/
theorem card_eq_card_add_sum_gain (F : ℕ → Finset α) (hF : ∀ i, F (i + 1) ⊆ F i) (N : ℕ) :
    (F 0).card = (F N).card + ∑ i ∈ range N, (F i \ F (i + 1)).card := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have h := card_sdiff_add_card_eq_card (hF k)
    omega

/-- **The count is the integral form of the step**: if the chain ends in the empty set and the
costs along it sum to `B`, then `B ≤ |F 0|` exactly when the costs sum to at most the gains. -/
theorem base_le_card_iff_sum_cost_le_sum_gain (F : ℕ → Finset α) (hF : ∀ i, F (i + 1) ⊆ F i)
    (N : ℕ) (hN : F N = ∅) (cost : ℕ → ℕ) (B : ℕ) (hB : ∑ i ∈ range N, cost i = B) :
    B ≤ (F 0).card ↔ ∑ i ∈ range N, cost i ≤ ∑ i ∈ range N, (F i \ F (i + 1)).card := by
  have h := card_eq_card_add_sum_gain F hF N
  rw [hN, card_empty, zero_add] at h
  rw [hB, h]

/-- **The step implies the count**: termwise `cost i ≤ gain i` gives `B ≤ |F 0|`. -/
theorem base_le_card_of_step (F : ℕ → Finset α) (hF : ∀ i, F (i + 1) ⊆ F i)
    (N : ℕ) (cost : ℕ → ℕ) (B : ℕ) (hB : ∑ i ∈ range N, cost i = B)
    (hstep : ∀ i ∈ range N, cost i ≤ (F i \ F (i + 1)).card) : B ≤ (F 0).card := by
  have h := card_eq_card_add_sum_gain F hF N
  have h2 : ∑ i ∈ range N, cost i ≤ ∑ i ∈ range N, (F i \ F (i + 1)).card :=
    Finset.sum_le_sum hstep
  omega

end PEqualNP.Outside.L_meta_951_aux.ChainSum
