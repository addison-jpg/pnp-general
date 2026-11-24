import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Functional pigeonhole principle: polynomial calculus upper bound of degree `N + 1`

For `N < m`, the system `funPHPSystem m N` has a polynomial calculus refutation of degree
`N + 1`. The proof is a case split on the hole of one pigeon: with `P` a monomial multiplier,
`P = ∑_{j ∈ H} X(a,j) * P + P * (pigeon axiom of a over H)`, and each `X(a,j) * P` is refuted
in the instance with pigeon `a` and hole `j` removed.
-/

namespace PEqualNP.ProofComplexity.FunPHPUpper

open PEqualNP.ProofComplexity MvPolynomial

section general
variable {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}

lemma two_eq_zero : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  have h : (C (2 : ZMod 2) : MvPolynomial σ (ZMod 2)) = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, C_0]
  rwa [show (C (2 : ZMod 2) : MvPolynomial σ (ZMod 2)) = 2 from map_ofNat C 2] at h

lemma deg_listprod (l : List σ) :
    ((l.map (fun v => (X v : MvPolynomial σ (ZMod 2)))).prod).totalDegree ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have : (X a : MvPolynomial σ (ZMod 2)).totalDegree ≤ 1 := by simp [totalDegree_X]
    omega

lemma mulList {p : MvPolynomial σ (ZMod 2)} (hp : PCDerivable F B p) (l : List σ)
    (h : l.length + p.totalDegree ≤ B) :
    PCDerivable F B ((l.map (fun v => (X v : MvPolynomial σ (ZMod 2)))).prod * p) := by
  induction l with
  | nil => simpa using hp
  | cons a t ih =>
    have ih' := ih (by simp only [List.length_cons] at h; omega)
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc]
    refine PCDerivable.mulX a ih' ?_
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (X a : MvPolynomial σ (ZMod 2)).totalDegree ≤ 1 := by simp [totalDegree_X]
    have h2 := totalDegree_mul
      ((t.map (fun v => (X v : MvPolynomial σ (ZMod 2)))).prod) p
    have h3 := deg_listprod (σ := σ) t
    simp only [List.length_cons] at h
    omega

lemma sum_deriv {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2))
    (h : ∀ i ∈ s, PCDerivable F B (f i)) : PCDerivable F B (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PCDerivable F B) (fun _ _ ha hb => PCDerivable.add ha hb)
    PCDerivable.zero h

end general

section main
variable {m N : ℕ}

lemma deg_pg (i : Fin m) (H : Finset (Fin N)) :
    ((∑ j ∈ H, (X (i, j) : MvPolynomial (Fin m × Fin N) (ZMod 2))) + 1).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  refine max_le ?_ (by simp)
  exact totalDegree_finsetSum_le fun j _ => by simp [totalDegree_X]

lemma key (B : ℕ) : ∀ (k : ℕ) (H : Finset (Fin N)) (A : Finset (Fin m))
    (l : List (Fin m × Fin N)), H.card = k → k + 1 ≤ A.card → l.length + k + 1 ≤ B →
    (∀ i ∈ A, PCDerivable (funPHPSystem m N) B
      ((l.map (fun v => (X v : MvPolynomial (Fin m × Fin N) (ZMod 2)))).prod *
        ((∑ j ∈ H, X (i, j)) + 1))) →
    PCDerivable (funPHPSystem m N) B
      ((l.map (fun v => (X v : MvPolynomial (Fin m × Fin N) (ZMod 2)))).prod) := by
  intro k
  induction k with
  | zero =>
    intro H A l hH hA hl h
    have hH0 : H = ∅ := Finset.card_eq_zero.mp hH
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    simpa [hH0] using h i hi
  | succ k ih =>
    intro H A l hH hA hl h
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    set P : MvPolynomial (Fin m × Fin N) (ZMod 2) :=
      (l.map (fun v => (X v : MvPolynomial (Fin m × Fin N) (ZMod 2)))).prod with hP
    have hsplit : P = ∑ j ∈ H, ((((a, j) :: l).map
        (fun v => (X v : MvPolynomial (Fin m × Fin N) (ZMod 2)))).prod)
        + P * ((∑ j ∈ H, X (a, j)) + 1) := by
      simp only [List.map_cons, List.prod_cons, ← hP]
      rw [← Finset.sum_mul]
      linear_combination (-(P * ∑ j ∈ H, (X (a, j) : MvPolynomial (Fin m × Fin N) (ZMod 2))))
        * (two_eq_zero (σ := Fin m × Fin N))
    rw [hsplit]
    refine PCDerivable.add (sum_deriv _ _ fun j hj => ?_) (h a ha)
    refine ih (H.erase j) (A.erase a) ((a, j) :: l) ?_ ?_ ?_ ?_
    · rw [Finset.card_erase_of_mem hj]; omega
    · rw [Finset.card_erase_of_mem ha]; omega
    · simp only [List.length_cons]; omega
    · intro i hi
      have hia : i ≠ a := (Finset.mem_erase.mp hi).1
      have hiA : i ∈ A := (Finset.mem_erase.mp hi).2
      have d1 := PCDerivable.mulX (a, j)
        (h i hiA) (by
          refine (totalDegree_mul _ _).trans ?_
          have h1 : (X (a, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
            simp [totalDegree_X]
          have h2 := totalDegree_mul P ((∑ j ∈ H, X (i, j)) + 1)
          have h3 : P.totalDegree ≤ l.length := deg_listprod (σ := Fin m × Fin N) l
          have h4 := deg_pg (m := m) (N := N) i H
          have : H.card = k + 1 := hH
          omega)
      have hax : (X (a, j) * X (i, j) : MvPolynomial (Fin m × Fin N) (ZMod 2))
          ∈ funPHPSystem m N :=
        Or.inr (Or.inr (Or.inl ⟨a, i, j, hia.symm, rfl⟩))
      have d2 := mulList (PCDerivable.ax (B := B) hax (by
          refine (totalDegree_mul _ _).trans ?_
          have h1 : (X (a, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
            simp [totalDegree_X]
          have h2 : (X (i, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
            simp [totalDegree_X]
          omega)) l (by
          refine le_trans (Nat.add_le_add_left (totalDegree_mul _ _) _) ?_
          have h1 : (X (a, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
            simp [totalDegree_X]
          have h2 : (X (i, j) : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
            simp [totalDegree_X]
          omega)
      have hS : (∑ j' ∈ H, (X (i, j') : MvPolynomial (Fin m × Fin N) (ZMod 2))) =
          X (i, j) + ∑ j' ∈ H.erase j, X (i, j') := (Finset.add_sum_erase H _ hj).symm
      have e : (((a, j) :: l).map
          (fun v => (X v : MvPolynomial (Fin m × Fin N) (ZMod 2)))).prod *
            ((∑ j' ∈ H.erase j, X (i, j')) + 1) =
          X (a, j) * (P * ((∑ j' ∈ H, X (i, j')) + 1)) + P * (X (a, j) * X (i, j)) := by
        simp only [List.map_cons, List.prod_cons, ← hP]
        rw [hS]
        linear_combination (-(X (a, j) * P * X (i, j))) *
          (two_eq_zero (σ := Fin m × Fin N))
      rw [e]
      exact PCDerivable.add d1 d2

end main

/-- For `N < m`, the functional pigeonhole system with `m` pigeons and `N` holes has a polynomial
calculus refutation of degree `N + 1`. -/
theorem funPHP_upper (m N : ℕ) (h : N < m) :
    PCRefutable (funPHPSystem m N) (N + 1) := by
  have := key (m := m) (N := N) (N + 1) N Finset.univ Finset.univ [] (by simp) (by simp; omega)
    (by simp) (fun i _ => by
      simpa using PCDerivable.ax (F := funPHPSystem m N)
        (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
        ((deg_pg (m := m) (N := N) i Finset.univ).trans (by omega)))
  simpa [PCRefutable] using this

end PEqualNP.ProofComplexity.FunPHPUpper
