import PEqualNP.Base.Blocker
import PEqualNP.W951.PureSDR

/-!
# TypeA: the I1 zero points of a set are the complements of minimal transversals

Research's type-A characterization (a) (`951/board/agents/research-typeA-menus.md`) for a
one-NOT circuit. Fix the NOT gate at `p` and read its input `h = hval gates p` on supports:
`hSet gates p A` is `h (canonPt A) = true`. It is monotone (`hSet_mono`, from `hval_mono`).

* `pureValid_one_canon_iff`: a world-1 pure option `(Z, 1)` with `Z = canonPt A` is valid for the
  set `R` iff `A` is disjoint from `R` and `h` is false at `A`.
* **`pureValid_one_max_iff`**: `canonPt A` is a valid world-1 option and no strictly larger
  support is, iff `A = (univ \ R) \ T` for a minimal transversal `T` of the minterms of `h`
  that avoid `R` (`Base.Blocker.isMaxFalse_iff`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Blocker

section TypeA

variable {n : ℕ} (gates : List Gate) (p : ℕ)

/-- The input `h` of the NOT gate at `p`, read on supports. -/
def hSet (A : Finset (Fin n)) : Prop := hval gates p (canonPt A) = true

theorem canonPt_mono {A B : Finset (Fin n)} (hAB : A ⊆ B) : canonPt A ≤ canonPt B := by
  intro c
  by_cases hc : c ∈ A
  · simp [canonPt, hc, hAB hc]
  · simp [canonPt, hc]

variable (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- `h` is monotone on supports. -/
theorem hSet_mono : Monotone (hSet (n := n) gates p) :=
  fun _ _ hAB h => hval_mono gates p hp hg hU hN (canonPt_mono hAB) h

include hN in
/-- A world-1 option at a canonical point is valid iff its support avoids `R` and `h` is false
there. -/
theorem pureValid_one_canon_iff (R A : Finset (Fin n)) :
    PureValid gates p R (.one (canonPt A)) ↔ Disjoint A R ∧ ¬ hSet gates p A := by
  simp only [PureValid, val_not_hval gates p hp hN, hSet, Bool.not_eq_true',
    Bool.not_eq_true, canonPt, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Finset.disjoint_right.mpr fun v hv hvA => h1 v hv hvA, by simp [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv hvA => Finset.disjoint_right.mp h1 hv hvA, by simpa using h2⟩

include hg hU hN in
/-- **Type-A (a) for circuits.** `canonPt A` is a valid world-1 option for `R` and no strictly
larger support is iff `A = (univ \ R) \ T` for a minimal transversal `T` of the minterms of the
NOT gate's input that avoid `R`. -/
theorem pureValid_one_max_iff (R A : Finset (Fin n)) :
    (PureValid gates p R (.one (canonPt A)) ∧
        ∀ B, A ⊂ B → ¬ PureValid gates p R (.one (canonPt B))) ↔
      ∃ T, IsMinTransversal (hSet gates p) R T ∧ A = (Finset.univ \ R) \ T := by
  rw [← isMaxFalse_iff (hSet_mono gates p hp hg hU hN), IsMaxFalse,
    pureValid_one_canon_iff gates p hp hN]
  simp only [pureValid_one_canon_iff gates p hp hN, not_and, not_not, and_assoc]

end TypeA

end PEqualNP.Outside.L_meta_951_aux
