import PEqualNP.Defs
import Mathlib.Tactic

/-!
# One hole, any number of pigeons: polynomial calculus degree 2

Row L-pcx-040 is the case of two pigeons. The same three axioms (pigeons `0` and `1`) refute the
functional pigeonhole system with `m ≥ 2` pigeons and one hole in degree 2.
-/

open PEqualNP.ProofComplexity MvPolynomial in
/-- `m ≥ 2` pigeons and one hole: a polynomial calculus refutation of degree 2. -/
theorem PEqualNP.ProofComplexity.Helpers.funPHP_one_hole (m : ℕ) (hm : 2 ≤ m) :
    PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.funPHPSystem m 1) 2 := by
  set p0 : Fin m := ⟨0, by omega⟩
  set p1 : Fin m := ⟨1, by omega⟩
  have h01 : p0 ≠ p1 := by simp [p0, p1, Fin.ext_iff]
  have h2 : (2 : MvPolynomial (Fin m × Fin 1) (ZMod 2)) = 0 := by
    have h : (C (2 : ZMod 2) : MvPolynomial (Fin m × Fin 1) (ZMod 2)) = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, C_0]
    rwa [show (C (2 : ZMod 2) : MvPolynomial (Fin m × Fin 1) (ZMod 2)) = 2 from map_ofNat C 2] at h
  have dX : ∀ v : Fin m × Fin 1, (X v : MvPolynomial (Fin m × Fin 1) (ZMod 2)).totalDegree ≤ 1 := by
    intro v; simp [totalDegree_X]
  have dA : ∀ v : Fin m × Fin 1, ((X v : MvPolynomial (Fin m × Fin 1) (ZMod 2)) + 1).totalDegree ≤ 1 := by
    intro v
    refine (totalDegree_add _ _).trans ?_
    simp [totalDegree_X]
  have a1 : PCDerivable (funPHPSystem m 1) 2 (X (p0, (0 : Fin 1)) + 1) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inr ⟨p0, by simp⟩))) ((dA _).trans (by norm_num))
  have a2 : PCDerivable (funPHPSystem m 1) 2 (X (p1, (0 : Fin 1)) + 1) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inr ⟨p1, by simp⟩))) ((dA _).trans (by norm_num))
  have a3 : PCDerivable (funPHPSystem m 1) 2
      (X (p0, (0 : Fin 1)) * X (p1, (0 : Fin 1))) :=
    PCDerivable.ax (Or.inr (Or.inr (Or.inl ⟨p0, p1, 0, h01, rfl⟩)))
      ((totalDegree_mul _ _).trans (by have := dX (p0, 0); have := dX (p1, 0); omega))
  have m1 := PCDerivable.mulX (p1, (0 : Fin 1)) a1
    ((totalDegree_mul _ _).trans (by have := dX (p1, 0); have := dA (p0, 0); omega))
  have s := PCDerivable.add (PCDerivable.add m1 a3) a2
  have e : X (p1, (0 : Fin 1)) * (X (p0, (0 : Fin 1)) + 1)
      + X (p0, (0 : Fin 1)) * X (p1, (0 : Fin 1))
      + (X (p1, (0 : Fin 1)) + 1) = (1 : MvPolynomial (Fin m × Fin 1) (ZMod 2)) := by
    linear_combination (X (p0, (0 : Fin 1)) * X (p1, (0 : Fin 1))
      + X (p1, (0 : Fin 1))) * h2
  unfold PCRefutable
  rw [← e]; exact s
