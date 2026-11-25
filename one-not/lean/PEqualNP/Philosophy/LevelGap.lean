import PEqualNP.Philosophy.Bridge

/-!
# The gap between the finite and the polynomial level (philosophy-unification seat)

HONESTY. A formal analogy, like `Bridge.lean`. It claims nothing about Beauvoir or Deleuze, and
it proves nothing about circuits: the statement is about arbitrary integer tables on the cubes of
`Fin 2`.

`collapse_iff_injective` is restated from `lean/PEqualNP/Philosophy/Unify.lean` (the source), in
identical form, because that file lives in the separate `lean/` Lake project.

Reading: Beauvoir's ambiguity (the refusal to identify the two sides of a situation), between the
levels. Along the projection from the finite table to its polynomial, "some table with this
polynomial has property `S`" and "every table with this polynomial has property `S`" are
different statements for some `S`, because the projection forgets (`virtualOf_not_injective`).
-/

namespace PEqualNP.Philosophy.Bridge

/-- Restated from `Unify.collapse_iff_injective`. -/
theorem collapse_iff_injective {X Y : Type*} (f : X → Y) :
    (∀ S : Set X, f '' S ⊆ Set.kernImage f S) ↔ Function.Injective f := by
  constructor
  · intro h x₁ x₂ e
    have := h {x₁} ⟨x₁, rfl, rfl⟩ e.symm
    exact (Set.mem_singleton_iff.1 this).symm
  · rintro hf S y ⟨x, hx, rfl⟩ x' e
    exact hf e ▸ hx

/-- **The levels do not collapse.** There is a property of slack-style tables on two points that
may hold at a polynomial without having to: possibility and necessity at the polynomial level
come apart. -/
theorem level_gap :
    ∃ S : Set (Finset (Fin 2) → ℤ), ¬ virtualOf (n := 2) '' S ⊆ Set.kernImage virtualOf S := by
  by_contra h
  exact virtualOf_not_injective
    ((collapse_iff_injective _).1 fun S => not_not.1 fun hS => h ⟨S, hS⟩)

end PEqualNP.Philosophy.Bridge
