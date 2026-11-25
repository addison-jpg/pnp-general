import Mathlib.Logic.Function.Basic

/-!
# Lawvere's fixed point theorem (the common spine of the lateral instances)

Classical: F. W. Lawvere, "Diagonal arguments and cartesian closed categories" (1969);
N. Yanofsky, "A universal approach to self-referential paradoxes, incompleteness and fixed points"
(2003). Mathlib already has the surjective form as `Function.exists_fixed_point_of_surjective`; we
reuse it and add the weaker, more flexible "diagonal" form that the instances need.
-/

namespace PEqualNP.Lateral

/-- Diagonal form: if the diagonal of `φ` post-composed with `g` is itself some row of `φ`,
then `g` has a fixed point. No surjectivity is needed, only that one row. -/
theorem lawvere_diag {A B : Type*} (φ : A → A → B) (g : B → B)
    (h : ∃ a, φ a = fun x => g (φ x x)) : ∃ b, g b = b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨φ a a, (congrFun ha a).symm⟩

/-- The surjective form, from Mathlib. -/
theorem lawvere_surjective {A B : Type*} (φ : A → A → B) (hφ : Function.Surjective φ)
    (g : B → B) : ∃ b, g b = b :=
  Function.exists_fixed_point_of_surjective φ hφ g

/-- Contrapositive (the form every instance uses): a fixed-point-free `g` rules out any
`φ` whose rows include the twisted diagonal. -/
theorem no_row_of_fixed_point_free {A B : Type*} (φ : A → A → B) (g : B → B)
    (hg : ∀ b, g b ≠ b) : ¬ ∃ a, φ a = fun x => g (φ x x) := fun h =>
  let ⟨b, hb⟩ := lawvere_diag φ g h
  hg b hb

/-- Contrapositive, surjective form. -/
theorem not_surjective_of_fixed_point_free {A B : Type*} (φ : A → A → B) (g : B → B)
    (hg : ∀ b, g b ≠ b) : ¬ Function.Surjective φ := fun h =>
  let ⟨b, hb⟩ := lawvere_surjective φ h g
  hg b hb

/-- `Not` has no fixed point on `Prop`. -/
theorem not_ne_self (p : Prop) : (¬ p) ≠ p := fun h => not_iff_self (Iff.of_eq h)

/-- `not` has no fixed point on `Bool`. -/
theorem bnot_ne_self (b : Bool) : (!b) ≠ b := by cases b <;> simp

end PEqualNP.Lateral
