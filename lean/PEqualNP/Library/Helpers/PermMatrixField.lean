import Mathlib
import PEqualNP.Defs

/-!
# L-lib-130 over any field

Row L-lib-130 is stated over the rationals. The proof uses the rationals only to see that the
sign of a permutation is not zero, which holds in every field (characteristic 2 included): if a
polynomial matrix evaluates at some point to a permutation matrix, its rows are linearly
independent over the fraction field.
-/

theorem PEqualNP.Library.PermMatrix.lin_indep_of_eval_perm :
    ∀ {σ ι : Type} {K0 : Type} [Field K0] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ K0))
      (x : σ → K0) (e : Equiv.Perm ι),
      (∀ a b : ι, (MvPolynomial.eval x) (M a b) = if e a = b then (1 : K0) else 0) →
      LinearIndependent (FractionRing (MvPolynomial σ K0))
        (fun a : ι => fun b : ι =>
          (algebraMap (MvPolynomial σ K0) (FractionRing (MvPolynomial σ K0))) (M a b)) := by
  intro σ ι K0 _ _ _ M x e heval
  let R := MvPolynomial σ K0
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hdet_eval : (MvPolynomial.eval x) M.det = (Equiv.Perm.sign e⁻¹ : K0) := by
    rw [RingHom.map_det]
    change (M.map (MvPolynomial.eval x)).det = _
    rw [Matrix.det_apply]
    rw [Finset.sum_eq_single e⁻¹]
    · simp [Matrix.map_apply, heval, Units.smul_def, zsmul_eq_mul]
    · intro τ _ hne
      have hex : ∃ i : ι, e (τ i) ≠ i := by
        by_contra hall
        push Not at hall
        apply hne
        ext i
        exact e.injective (by simp [hall i])
      obtain ⟨i, hi⟩ := hex
      have hprod : ∏ j : ι, (M.map (MvPolynomial.eval x)) (τ j) j = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [Matrix.map_apply, heval, hi]
      rw [hprod, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdet_ne : M.det ≠ 0 := by
    intro h0
    have hsign : ((Equiv.Perm.sign e⁻¹ : ℤ) : K0) = 0 := by
      rw [← hdet_eval, h0, map_zero]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e⁻¹) with h1 | h1 <;> simp [h1] at hsign
  have hM_K_det : (M.map φ).det ≠ 0 := by
    have hdet_map : (M.map φ).det = φ M.det := (RingHom.map_det φ M).symm
    rw [hdet_map]
    intro h0
    exact hdet_ne (IsFractionRing.injective R K (h0.trans (map_zero φ).symm))
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hvec : Matrix.vecMul c (M.map φ) = 0 := by
    ext b
    have hcb := congrFun hc b
    simpa [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.map_apply] using hcb
  have hinv : M.map φ * (M.map φ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (M.map φ) (isUnit_iff_ne_zero.mpr hM_K_det)
  have hc0 : c = 0 := by
    calc
      c = Matrix.vecMul c (1 : Matrix ι ι K) := by simp
      _ = Matrix.vecMul c (M.map φ * (M.map φ)⁻¹) := by rw [hinv]
      _ = Matrix.vecMul (Matrix.vecMul c (M.map φ)) (M.map φ)⁻¹ := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := by rw [hvec, Matrix.zero_vecMul]
  exact congrFun hc0 a
