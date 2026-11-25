import PEqualNP.Lateral.Lawvere
import Mathlib.Computability.Halting

/-!
# Halting-flavoured instances

1. `no_computable_enumeration`: derived from the Lawvere lemma. No computable two-argument
   function enumerates all computable unary functions.
2. `halting_bridge`: Mathlib's `ComputablePred.halting_problem` restated. It is NOT re-derived from
   Lawvere here: Mathlib proves it through Rice's theorem. The honest link is analogy: the
   standard proof diagonalises exactly as in (1).
-/

namespace PEqualNP.Lateral

/-- No computable `e : ℕ → ℕ → ℕ` has every computable unary function as a row. Lawvere with
`g = succ` and the row `x ↦ e x x + 1`. -/
theorem no_computable_enumeration (e : ℕ → ℕ → ℕ) (he : Computable₂ e) :
    ¬ ∀ f : ℕ → ℕ, Computable f → ∃ a, e a = f := by
  intro h
  have hc : Computable (fun x => e x x + 1) :=
    Computable.succ.comp (he.comp Computable.id Computable.id)
  obtain ⟨a, ha⟩ := h _ hc
  exact no_row_of_fixed_point_free e Nat.succ (fun n => Nat.succ_ne_self n)
    ⟨a, funext fun x => congrFun ha x⟩

/-- Mathlib's halting problem theorem, restated (bridge, not a re-proof). -/
theorem halting_bridge (n : ℕ) :
    ¬ ComputablePred fun c => (Nat.Partrec.Code.eval c n).Dom :=
  ComputablePred.halting_problem n

end PEqualNP.Lateral
