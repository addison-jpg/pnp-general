import PEqualNP.Defs
import Mathlib.Tactic

/-!
# No one-line Res(+) refutation of a formula without the empty clause

Row L-pcx-016 is the case `PHP 2 1`. A Res(+) refutation of one line is a single axiom, so every
Res(+) refutation of any CNF `F` with `∅ ∉ F` has at least two lines; in particular every
pigeonhole formula `PHP m n` with `n ≥ 1`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem lin_refutation_len {V : Type} [DecidableEq V] (F : Set (Clause V))
    (hF : (∅ : Clause V) ∉ F) (π : List (LinClause V)) (h : IsLinRefutation F π) :
    1 < π.length := by
  obtain ⟨hd, hmem⟩ := h
  cases hd with
  | nil => simp at hmem
  | @ax π' C hπ hC =>
    cases π' with
    | nil =>
      simp only [List.mem_singleton] at hmem
      obtain ⟨C0, hC0, hEq⟩ := hC
      exfalso
      have hC0e : C0 = ∅ := by
        simp only [linOfClause] at hEq
        rw [← hmem] at hEq
        exact Finset.image_eq_empty.mp hEq
      exact hF (hC0e ▸ hC0)
    | cons a t => simp
  | @res π' C D R hπ hC hD hR =>
    cases π' with
    | nil => simp at hC
    | cons a t => simp
  | @weak π' C D hπ hC hW =>
    cases π' with
    | nil => simp at hC
    | cons a t => simp

theorem php_no_empty (m n : ℕ) (hn : 1 ≤ n) : (∅ : Clause (Fin m × Fin n)) ∉ PHP m n := by
  rintro (⟨i, h⟩ | ⟨i, i', j, -, h⟩)
  · have : ((i, (⟨0, hn⟩ : Fin n)), true) ∈ (∅ : Clause (Fin m × Fin n)) := by
      rw [h]; simp
    simp at this
  · have : ((i, j), false) ∈ (∅ : Clause (Fin m × Fin n)) := by
      rw [h]; simp
    simp at this

/-- L-pcx-016 for every pigeonhole formula with at least one hole. -/
theorem php_lin_len (m n : ℕ) (hn : 1 ≤ n) (π : List (LinClause (Fin m × Fin n)))
    (h : IsLinRefutation (PHP m n) π) : 1 < π.length :=
  lin_refutation_len _ (php_no_empty m n hn) π h

end PEqualNP.ProofComplexity.Helpers
