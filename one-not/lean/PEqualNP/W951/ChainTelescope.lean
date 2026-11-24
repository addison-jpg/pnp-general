import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Logic.Function.Iterate

/-!
# The telescoping path (common form of README items L5 and L6) and the k-point step (C3)

* `sum_increments`: in any additive commutative group the increments of a path `x 0, …, x N`
  sum to `x N - x 0`.  README L5 is the instance `x i = - slack (Q i)` in `ℤ` (the increments are
  `gain - cost`); README L6 is the instance `x k = f^[k] x₀` in a vector space, where the sum is
  `(n + 1) • (f a - a)` for the Cesàro mean `a` of an affine `f`.
* `sum_gain_sub_cost`, `orbit_sum_displacement`: the two instances, stated.
* `kstep_of_slack_nonneg`: the converse of `ChainSum.slack_nonneg_of_descent` (README L7).  If the
  slack is nonnegative at a cube and vanishes at a cube of smaller base (the last cube of a
  chain), that cube is a step.  So without a bound on the number of points the k-point step IS
  the count; the content of Conjecture C3 for a fixed `k` is the bound `k` alone.
-/

namespace PEqualNP.Outside.L_meta_951_aux.ChainTelescope

open Finset

/-- **Telescoping path**: the increments of a path sum to the difference of its ends. -/
theorem sum_increments {G : Type*} [AddCommGroup G] (x : ℕ → G) (N : ℕ) :
    ∑ i ∈ range N, (x (i + 1) - x i) = x N - x 0 :=
  Finset.sum_range_sub x N

/-- The chain sum in the form used for the slack: decreasing increments. -/
theorem sum_steps_slack (slack : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range N, (slack i - slack (i + 1)) = slack 0 - slack N :=
  Finset.sum_range_sub' slack N

/-- **README L5 as an instance**: with `slack i` the slack of the `i`-th cube of a chain and
`slack i - slack (i + 1) = gain i - cost i`, the terms `gain - cost` sum to the difference of the
slacks of the two ends. -/
theorem sum_gain_sub_cost (slack gain cost : ℕ → ℤ) (N : ℕ)
    (h : ∀ i, i < N → slack i - slack (i + 1) = gain i - cost i) :
    ∑ i ∈ range N, (gain i - cost i) = slack 0 - slack N := by
  rw [← sum_steps_slack slack N]
  exact (Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)).symm

/-- **README L6 as an instance** (unnormalised): for an additive map `f`, the displacement of the
sum of the first `n + 1` points of an orbit is the difference of the ends of the orbit.  Dividing
by `n + 1` gives `f a - a = (n + 1)⁻¹ (f^[n + 1] x₀ - x₀)` for the Cesàro mean `a`. -/
theorem orbit_sum_displacement {G : Type*} [AddCommGroup G] (f : G →+ G) (x₀ : G) (n : ℕ) :
    f (∑ k ∈ range (n + 1), f^[k] x₀) - ∑ k ∈ range (n + 1), f^[k] x₀ = f^[n + 1] x₀ - x₀ := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  have h : ∀ k, f (f^[k] x₀) - f^[k] x₀ = f^[k + 1] x₀ - f^[k] x₀ := fun k => by
    rw [Function.iterate_succ_apply']
  simp_rw [h]
  exact sum_increments (fun k => f^[k] x₀) (n + 1)

/-- **The unbounded step is the count**: if the slack is nonnegative at `Q` and some cube `E`
of smaller base has slack `0`, then `E` is a step from `Q`. -/
theorem kstep_of_slack_nonneg {C : Type*} (base : C → ℕ) (slack : C → ℤ) (Q E : C)
    (hQ : 0 ≤ slack Q) (hE : slack E = 0) (hb : base E < base Q) :
    ∃ Q', base Q' < base Q ∧ slack Q' ≤ slack Q :=
  ⟨E, hb, by omega⟩

end PEqualNP.Outside.L_meta_951_aux.ChainTelescope
