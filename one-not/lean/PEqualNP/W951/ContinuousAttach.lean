import PEqualNP.W951.F2Induct

/-!
# Where the continuous form attaches to the remaining `sorry` (README items L5, C2; task continuous-mapping)

The one unproved declaration under `L_meta_951` is `no_minCE`. `no_minCE_of_MUF2` (F2Induct.lean)
proves it from the count `MUF2 S gates`, i.e. `∑ w, (|S w| - 1) ≤ |F2 gates S ∅|`, for every minimal
counterexample. This file states the same attachment for the slack and for its product-measure
average `Φ`:

* `slack gates S Q = |F2 gates S Q| - baseDQ S ∅ Q` (an integer);
* `Phi gates S p = ∑ Q, p ^ |Q| * (1 - p) ^ (n - |Q|) * slack gates S Q` (a real polynomial in `p`);
* `Phi_zero : Phi gates S 0 = slack gates S ∅`;
* `no_minCE_of_Phi_zero_nonneg`: if `0 ≤ Phi gates S 0` in every minimal counterexample, there is none.

So any continuous statement about `Φ` proves the theorem exactly when it yields `0 ≤ Φ 0` for a
minimal counterexample. Nothing here proves that inequality.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open Finset
open PEqualNP.CircuitLowerBounds

variable {n m : ℕ}

/-- The slack of a cube: real-witness gates minus the monotone optimum of the cube. -/
noncomputable def slack (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : ℤ :=
  ((F2 gates S Q).card : ℤ) - (baseDQ S ∅ Q : ℤ)

/-- The product-measure average of the slack: each point is in `Q` independently with probability `p`. -/
noncomputable def Phi (gates : List Gate) (S : Fin m → Finset (Fin n)) (p : ℝ) : ℝ :=
  ∑ Q : Finset (Fin n), p ^ Q.card * (1 - p) ^ (n - Q.card) * (slack gates S Q : ℝ)

/-- At `p = 0` the average is the slack of the empty cube. -/
theorem Phi_zero (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    Phi gates S 0 = (slack gates S ∅ : ℝ) := by
  unfold Phi
  rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
  · simp
  · intro Q _ hQ
    have : Q.card ≠ 0 := by simpa [Finset.card_eq_zero] using hQ
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The attachment**: the count for a minimal counterexample is `0 ≤ slack ∅`. -/
theorem no_minCE_of_slack_nonneg
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → 0 ≤ slack gates S ∅) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MUF2 fun n m S gates out M => by
    have h := H n m S gates out M
    unfold slack at h
    rw [baseDQ_empty] at h
    unfold MUF2
    omega

/-- **The continuous attachment**: if `0 ≤ Φ(0)` in every minimal counterexample, there is none. -/
theorem no_minCE_of_Phi_zero_nonneg
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → 0 ≤ Phi gates S 0) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_slack_nonneg fun n m S gates out M => by
    have h := H n m S gates out M
    rw [Phi_zero] at h
    exact_mod_cast h

end PEqualNP.Outside.L_meta_951_aux
