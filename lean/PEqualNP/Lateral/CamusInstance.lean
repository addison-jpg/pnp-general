import PEqualNP.Lateral.Lawvere
import PEqualNP.Philosophy.Camus

/-!
# Camus's `no_total_answer` from the common lemma

Camus.lean is untouched; it proved the fixed point lemma locally. Here the same statement is
re-derived from `lawvere_surjective` (Mathlib), and checked equal to the original.
-/

namespace PEqualNP.Lateral

theorem camus_from_lawvere (M : Type*) : ¬ ∃ φ : M → M → Prop, Function.Surjective φ := by
  rintro ⟨φ, hφ⟩
  exact not_surjective_of_fixed_point_free φ Not not_ne_self hφ

/-- The two derivations prove the same statement. -/
theorem camus_agrees (M : Type*) :
    (¬ ∃ φ : M → M → Prop, Function.Surjective φ) ↔
      (¬ ∃ φ : M → M → Prop, Function.Surjective φ) :=
  ⟨fun _ => camus_from_lawvere M, fun _ => PEqualNP.Philosophy.Camus.no_total_answer M⟩

end PEqualNP.Lateral
