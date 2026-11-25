import PEqualNP.Lateral.Lawvere

/-!
# Cantor and Russell as instances of the Lawvere lemma
-/

namespace PEqualNP.Lateral

/-- Cantor: no surjection `A → Set A`, from `lawvere_surjective` with `g = Not`. -/
theorem cantor_from_lawvere {A : Type*} (f : A → Set A) : ¬ Function.Surjective f := by
  intro hf
  have : Function.Surjective (fun a x => x ∈ f a : A → A → Prop) := by
    intro P
    obtain ⟨a, ha⟩ := hf {x | P x}
    exact ⟨a, by funext x; exact propext (Set.ext_iff.mp ha x)⟩
  exact not_surjective_of_fixed_point_free _ Not not_ne_self this

/-- Russell: for any binary "membership" relation `r` on `A`, some property of elements is not the
extension of any element, namely `x ↦ ¬ r x x`. So "every property is a set" is inconsistent
(naive comprehension), by `no_row_of_fixed_point_free`. -/
theorem russell_from_lawvere {A : Type*} (r : A → A → Prop) :
    ¬ ∀ P : A → Prop, ∃ a, ∀ x, r a x ↔ P x := by
  intro h
  obtain ⟨a, ha⟩ := h (fun x => ¬ r x x)
  exact no_row_of_fixed_point_free r Not not_ne_self
    ⟨a, funext fun x => propext (ha x)⟩

end PEqualNP.Lateral
