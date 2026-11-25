import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureLLift
import PEqualNP.W951.CanonOneNot

/-!
# F2Bridge: lifted witnesses ⇒ real witnesses (for the F2 count, coord 12:46)

The point induction counts F2: real OR gates `r` with a REAL witness (`Z` avoiding the set, `Q`
fixed to `1`, `r(Z) = 0`, `r(Z + e_u) = r(Z + e_u') = 1`). The paper constructions (front A2's G1 / GL)
produce LIFTED witnesses (zero point and atoms in the lift `M(x, y)`). This file is the bridge.

* `val_lowerWire`: the real wire `lowerWire n p i` of a lifted gate wire `i` takes at `x` the lifted
  value at `(x, ν x)` (`nuPt`).
* `real_zero_of_lift`, `real_one_of_lift`: a lifted wire `0` at some `ζ ≥ (Z, ν Z)` is `0` at `Z` in the
  real circuit; a lifted wire `1` at some `α ≤ (Z + e_u, ν(Z + e_u))` is `1` at `Z + e_u`. So a lifted
  witness with a CONSISTENT zero point (one above `(Z, ν Z)`, e.g. a world-0 zero point with `h(Z) = 1`)
  and atoms below the consistent unit points is a real witness at `Z`.
* `real_one_of_C0`: exclusion — a lifted wire with `C_0 = 1` at `(Q ∪ {v}, 0)` is `1` in the real
  circuit at every `Z ⊇ Q ∪ {v}`, so it has no real witness with `Q ∪ {v}` fixed to `1`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section F2Bridge

variable {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

theorem liftWire_lowerWire (i : ℕ) (hi : n + 1 ≤ i) : liftWire n p (lowerWire n p i) = i := by
  unfold lowerWire
  rw [liftWire_realWire]
  omega

include hp in
/-- The real wire of a lifted gate wire `i` is the lifted wire at `(x, ν x)`. -/
theorem val_lowerWire (x : Fin n → Bool) (i : ℕ) (hi : n + 1 ≤ i) :
    val gates x (lowerWire n p i) = val (lift n p gates) (nuPt gates p x) i := by
  rw [val_lift (n := n) gates p hp x (lowerWire n p i), liftWire_lowerWire p i hi]
  rfl

include hp hg hU hN in
/-- **Bridge, zero point**: a lifted wire `0` at a point above `(Z, ν Z)` is `0` at `Z` in the real
circuit. -/
theorem real_zero_of_lift {i : ℕ} (hi : n + 1 ≤ i) {Z : Fin n → Bool} {ζ : Fin (n + 1) → Bool}
    (hle : nuPt gates p Z ≤ ζ) (hζ : val (lift n p gates) ζ i = false) :
    val gates Z (lowerWire n p i) = false := by
  rw [val_lowerWire gates p hp Z i hi]
  exact val_false_of_le _ (monoList_lift (n := n) gates p hp hg hU hN).andOr hle hζ

include hp hg hU hN in
/-- **Bridge, atoms**: a lifted wire `1` at a point below `(y, ν y)` is `1` at `y` in the real
circuit. -/
theorem real_one_of_lift {i : ℕ} (hi : n + 1 ≤ i) {y : Fin n → Bool} {α : Fin (n + 1) → Bool}
    (hle : α ≤ nuPt gates p y) (hα : val (lift n p gates) α i = true) :
    val gates y (lowerWire n p i) = true := by
  rw [val_lowerWire gates p hp y i hi]
  have h := val_le_of_le _ (monoList_lift (n := n) gates p hp hg hU hN).andOr hle i
  rw [hα] at h
  cases hv : val (lift n p gates) (nuPt gates p y) i
  · rw [hv] at h; exact absurd h (by decide)
  · rfl

include hp hg hU hN in
/-- **Exclusion** (the F2 form of Lemma C0 / L-U_v): a lifted wire with `C_0 = 1` at `(Q ∪ {v}, 0)` is
`1` in the real circuit at every point `Z ⊇ Q ∪ {v}`. -/
theorem real_one_of_C0 {i : ℕ} (hi : n + 1 ≤ i) (Q : Finset (Fin n)) (v : Fin n)
    (h0 : val (lift n p gates) (ext (canonPt (insert v Q)) false) i = true) {Z : Fin n → Bool}
    (hZ : ∀ x ∈ insert v Q, Z x = true) : val gates Z (lowerWire n p i) = true :=
  real_one_of_lift gates p hp hg hU hN hi
    (ext_le_of_le (canonPt_le hZ) (Bool.false_le _)) h0

end F2Bridge

end PEqualNP.Outside.L_meta_951_aux
