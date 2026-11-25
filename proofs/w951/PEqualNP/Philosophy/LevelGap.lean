import PEqualNP.Philosophy.Bridge

/-!
# The gap between the finite and the polynomial level (philosophy-unification seat)

HONESTY. A formal analogy, like `Bridge.lean`. It claims nothing about Beauvoir or Deleuze, and
it proves nothing about circuits: the statement is about arbitrary integer tables on the cubes of
`Fin 2`. The label "Beauvoir's ambiguity" was removed after review: Beauvoir's ambiguity is not
about functions.

`collapse_iff_injective` is restated from `proofs/main/PEqualNP/Philosophy/Unify.lean` (the source), in
identical form, because that file lives in the separate `proofs/main/` Lake project.

Content: a generic fact (`image ⊆ kernImage` for all `S` iff injective). Along the projection
from an integer table on `Fin 2` to its polynomial, "some table with this polynomial has property
`S`" and "every table with this polynomial has property `S`" are different statements for some
`S`, because `virtualOf` is not injective (`virtualOf_not_injective`).
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

/-- For some set `S` of integer tables on `Fin 2`, the image of `S` under `virtualOf` is not inside
its kernel image. Generic, from non-injectivity of `virtualOf` on arbitrary tables; no claim
about slack tables of circuits. -/
theorem level_gap :
    ∃ S : Set (Finset (Fin 2) → ℤ), ¬ virtualOf (n := 2) '' S ⊆ Set.kernImage virtualOf S := by
  by_contra h
  exact virtualOf_not_injective
    ((collapse_iff_injective _).1 fun S => not_not.1 fun hS => h ⟨S, hS⟩)

end PEqualNP.Philosophy.Bridge
