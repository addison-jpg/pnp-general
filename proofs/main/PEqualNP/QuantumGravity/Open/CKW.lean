import PEqualNP.Philosophy.BeauvoirQG

/-!
# Coffman–Kundu–Wootters monogamy for three qubits (seat O2)

For every pure state `ψ` of three qubits A, B, C,

  `C(ρ_AB)² + C(ρ_AC)² + 4 |Det ψ| = 4 det ρ_A`,

where `C` is Wootters' concurrence (defined from the eigenvalues of `ρ ρ̃`, with the spin flip
`ρ̃ = (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)`), `Det` is Cayley's hyperdeterminant of the 2×2×2 amplitude
array, and `4 det ρ_A = τ_{A|BC}` is the tangle of A against BC. Hence the CKW inequality

  `τ_{AB} + τ_{AC} ≤ τ_{A|BC}`,   `τ_{AB} = C(ρ_AB)²`,

and the residual is the three-tangle `τ_{ABC} = 4 |Det ψ|`.

No normalisation is assumed: all three sides are homogeneous of degree 4 in the amplitudes, so the
statement holds for every amplitude array, and for unit vectors it is the physical statement.

The reduced states are those of `BeauvoirQG` (reviewed as faithful): `ρ_AB = selfState ψ`
(`ψ` read as a matrix `(A × B) × C`), `ρ_AC = reduceAC ψ`, and `ρ_A = selfState` of `ψ` read as a
matrix `A × (B × C)`.

Route (CKW 2000). A rank-two `ρ = V Vᴴ` (`V` a 4×2 matrix) has
`charpoly (ρ ρ̃) = X² · charpoly (T̄ T)` with `T = Vᵀ (σ_y ⊗ σ_y) V` symmetric 2×2
(`Matrix.charpoly_mul_comm'`), so the four `λ`s are `s₁ ≥ s₂ ≥ 0 = 0` with `s₁² + s₂² = ‖T‖²_F`
and `s₁ s₂ = |det T|`; hence `C² = ‖T‖²_F − 2 |det T|` (`concurrence_sq_rankTwo`). The rest is
polynomial algebra in the 8 amplitudes: `det T_AB = det T_AC = −Det ψ` and
`‖T_AB‖²_F + ‖T_AC‖²_F = 4 det ρ_A`.

Physics: V. Coffman, J. Kundu and W. K. Wootters, Phys. Rev. A 61 (2000) 052306;
W. K. Wootters, Phys. Rev. Lett. 80 (1998) 2245 (cited from memory; read status research/LITERATURE.md §M6).
-/

namespace PEqualNP.QuantumGravity.Open.CKW

open Matrix Polynomial PEqualNP.Philosophy.BeauvoirQG
open scoped ComplexConjugate Kronecker

/-- Two qubits. -/
abbrev Q2 := Fin 2 × Fin 2

/-- The Pauli matrix `σ_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- `σ_y ⊗ σ_y` on two qubits. -/
def sigmaYY : Matrix Q2 Q2 ℂ := sigmaY ⊗ₖ sigmaY

/-- Wootters' spin flip `ρ̃ = (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)`, with `ρ*` the entrywise complex
conjugate in the computational basis. -/
def spinFlip (ρ : Matrix Q2 Q2 ℂ) : Matrix Q2 Q2 ℂ := sigmaYY * ρ.map conj * sigmaYY

/-- **Wootters' concurrence** of a two-qubit state `ρ`: with `λ₁ ≥ λ₂ ≥ λ₃ ≥ λ₄` the square roots
of the eigenvalues of `ρ ρ̃` (the roots of its characteristic polynomial, with multiplicity),
`C(ρ) = max(0, λ₁ − λ₂ − λ₃ − λ₄) = max(0, 2 λ_max − Σ λ)`. The eigenvalues of `ρ ρ̃` are real and
nonnegative for a state; we take the real part before the square root. -/
noncomputable def concurrence (ρ : Matrix Q2 Q2 ℂ) : ℝ :=
  let l := (ρ * spinFlip ρ).charpoly.roots.map fun z : ℂ => Real.sqrt z.re
  max 0 (2 * l.fold max 0 - l.sum)

/-- The squared Frobenius norm of a matrix. -/
noncomputable def frob {n : Type*} [Fintype n] (T : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (T i j)

/-- The 2×2 matrix `T = Vᵀ (σ_y ⊗ σ_y) V`, `T_kl = ⟨ṽ_k | v_l⟩` (the "tilde inner products" of
the two unnormalised vectors that span the range of `ρ = V Vᴴ`). -/
def tMat (V : Matrix Q2 (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Vᵀ * sigmaYY * V

theorem sigmaYY_map_conj : sigmaYY.map conj = sigmaYY := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sigmaYY, sigmaY, kroneckerMap_apply]

theorem sigmaYY_transpose : sigmaYYᵀ = sigmaYY := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sigmaYY, sigmaY, kroneckerMap_apply]

theorem tMat_apply (V : Matrix Q2 (Fin 2) ℂ) (k l : Fin 2) :
    tMat V k l = -(V (0, 0) k * V (1, 1) l) + V (0, 1) k * V (1, 0) l + V (1, 0) k * V (0, 1) l
      - V (1, 1) k * V (0, 0) l := by
  simp only [tMat, Matrix.mul_apply, transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    sigmaYY, sigmaY, kroneckerMap_apply]
  simp
  ring_nf

theorem tMat_symm (V : Matrix Q2 (Fin 2) ℂ) (k l : Fin 2) : tMat V k l = tMat V l k := by
  rw [tMat_apply, tMat_apply]; ring

/-! ## Concurrence of a rank-two state -/

theorem conjTranspose_map_conj (V : Matrix Q2 (Fin 2) ℂ) : Vᴴ.map conj = Vᵀ := by
  ext i j; simp [conjTranspose_apply]

theorem transpose_map_conj (V : Matrix Q2 (Fin 2) ℂ) : Vᵀ.map conj = Vᴴ := by
  ext i j; simp [conjTranspose_apply]

theorem mul_spinFlip_eq (V : Matrix Q2 (Fin 2) ℂ) :
    (V * Vᴴ) * spinFlip (V * Vᴴ) = V * (Vᴴ * sigmaYY * V.map conj * Vᵀ * sigmaYY) := by
  simp only [spinFlip, Matrix.map_mul, conjTranspose_map_conj, Matrix.mul_assoc]

theorem spinFlip_mul_comm_eq (V : Matrix Q2 (Fin 2) ℂ) :
    (Vᴴ * sigmaYY * V.map conj * Vᵀ * sigmaYY) * V = (tMat V).map conj * tMat V := by
  simp only [tMat, Matrix.map_mul, transpose_map_conj, sigmaYY_map_conj, Matrix.mul_assoc]

/-- The characteristic polynomial of `ρ ρ̃` for `ρ = V Vᴴ`: two zero roots and those of `T̄ T`. -/
theorem charpoly_rankTwo (V : Matrix Q2 (Fin 2) ℂ) :
    ((V * Vᴴ) * spinFlip (V * Vᴴ)).charpoly = X ^ 2 * ((tMat V).map conj * tMat V).charpoly := by
  have h : X ^ Fintype.card (Fin 2) * (V * (Vᴴ * sigmaYY * V.map conj * Vᵀ * sigmaYY)).charpoly =
      X ^ Fintype.card Q2 * ((Vᴴ * sigmaYY * V.map conj * Vᵀ * sigmaYY) * V).charpoly :=
    charpoly_mul_comm' V _
  have c2 : Fintype.card (Fin 2) = 2 := rfl
  have c4 : Fintype.card Q2 = 2 + 2 := rfl
  rw [c2, c4, ← mul_spinFlip_eq, spinFlip_mul_comm_eq, pow_add, mul_assoc] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero) h

theorem trace_tbarT (V : Matrix Q2 (Fin 2) ℂ) :
    ((tMat V).map conj * tMat V).trace = (frob (tMat V) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, frob,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [tMat_symm V j i, mul_comm, Complex.mul_conj]

theorem det_tbarT (V : Matrix Q2 (Fin 2) ℂ) :
    ((tMat V).map conj * tMat V).det = ((‖(tMat V).det‖ ^ 2 : ℝ) : ℂ) := by
  have h : ((tMat V).map conj).det = conj (tMat V).det := by
    rw [RingHom.map_det]; rfl
  rw [Matrix.det_mul, h, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]

theorem two_norm_det_le_frob (V : Matrix Q2 (Fin 2) ℂ) :
    2 * ‖(tMat V).det‖ ≤ frob (tMat V) := by
  have hs := tMat_symm V 0 1
  have hd : ‖(tMat V).det‖ ≤ ‖tMat V 0 0‖ * ‖tMat V 1 1‖ + ‖tMat V 0 1‖ * ‖tMat V 1 0‖ := by
    rw [det_fin_two]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  simp only [frob, Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
  rw [← hs] at hd ⊢
  nlinarith [sq_nonneg (‖tMat V 0 0‖ - ‖tMat V 1 1‖)]

/-- **Concurrence of a rank-two two-qubit state** `ρ = V Vᴴ`:
`C(ρ)² = ‖T‖²_F − 2 |det T|`, `T = Vᵀ (σ_y ⊗ σ_y) V`. -/
theorem concurrence_sq_rankTwo (V : Matrix Q2 (Fin 2) ℂ) :
    concurrence (V * Vᴴ) ^ 2 = frob (tMat V) - 2 * ‖(tMat V).det‖ := by
  set F := frob (tMat V)
  set D := ‖(tMat V).det‖
  have hFD := two_norm_det_le_frob V
  have hD : 0 ≤ D := norm_nonneg _
  set u := Real.sqrt (F + 2 * D)
  set v := Real.sqrt (F - 2 * D)
  have hu2 : u ^ 2 = F + 2 * D := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = F - 2 * D := Real.sq_sqrt (by linarith)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  set s₁ := (u + v) / 2
  set s₂ := (u - v) / 2
  have h1 : 0 ≤ s₁ := by positivity
  have h2 : 0 ≤ s₂ := by simp only [s₂]; linarith
  have h12 : s₂ ≤ s₁ := by simp only [s₁, s₂]; linarith
  have hsum : s₁ ^ 2 + s₂ ^ 2 = F := by simp only [s₁, s₂]; nlinarith
  have hprod : s₁ ^ 2 * s₂ ^ 2 = D ^ 2 := by
    have : s₁ * s₂ = D := by simp only [s₁, s₂]; nlinarith
    rw [← mul_pow, this]
  have hcp : ((V * Vᴴ) * spinFlip (V * Vᴴ)).charpoly =
      (({0, 0, ((s₁ ^ 2 : ℝ) : ℂ), ((s₂ ^ 2 : ℝ) : ℂ)} : Multiset ℂ).map fun a => X - C a).prod := by
    rw [charpoly_rankTwo, charpoly_fin_two, trace_tbarT, det_tbarT]
    have eF : (F : ℂ) = ((s₁ ^ 2 : ℝ) : ℂ) + ((s₂ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, hsum]
    have eD : ((D ^ 2 : ℝ) : ℂ) = ((s₁ ^ 2 : ℝ) : ℂ) * ((s₂ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hprod]
    rw [eF, eD]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, C_add, C_mul, C_0, sub_zero]
    ring
  have hroots : (((V * Vᴴ) * spinFlip (V * Vᴴ)).charpoly.roots.map
      fun z : ℂ => Real.sqrt z.re) = {0, 0, s₁, s₂} := by
    rw [hcp, roots_multiset_prod_X_sub_C]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Complex.ofReal_re, Complex.zero_re, Real.sqrt_zero, Real.sqrt_sq h1, Real.sqrt_sq h2]
  have hC : concurrence (V * Vᴴ) = v := by
    unfold concurrence
    simp only [hroots]
    simp only [Multiset.insert_eq_cons, Multiset.fold_cons_left, Multiset.fold_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    rw [max_eq_left h2, max_eq_left h12, max_eq_right h1, max_eq_right h1]
    have : 2 * s₁ - (0 + (0 + (s₁ + s₂))) = v := by simp only [s₁, s₂]; ring
    rw [this, max_eq_right hv0]
  rw [hC, hv2]

/-! ## Three qubits -/

section ThreeQubits

variable (ψ : Matrix Q2 (Fin 2) ℂ)

/-- `ψ` read as the matrix of the cut `A | BC`. -/
def splitA : Matrix (Fin 2) Q2 ℂ := fun x p => ψ (x, p.1) p.2

/-- The reduced state of qubit A, `ρ_A = Tr_BC |ψ⟩⟨ψ|`. -/
def rhoA : Matrix (Fin 2) (Fin 2) ℂ := selfState (splitA ψ)

/-- The tangle of A against BC, `τ_{A|BC} = 4 det ρ_A` (CKW 2000). -/
noncomputable def tangleA : ℝ := 4 * (rhoA ψ).det.re

/-- `ψ` read as a matrix `(A × C) × B`; `ρ_AC = vAC ψ (vAC ψ)ᴴ`. -/
def vAC : Matrix Q2 (Fin 2) ℂ := fun p y => ψ (p.1, y) p.2

/-- Cayley's hyperdeterminant of the 2×2×2 array `a_ijk = ψ (i, j) k`. -/
def hyperdet : ℂ :=
  let a := fun i j k => ψ (i, j) k
  (a 0 0 0 ^ 2 * a 1 1 1 ^ 2 + a 0 0 1 ^ 2 * a 1 1 0 ^ 2 + a 0 1 0 ^ 2 * a 1 0 1 ^ 2
      + a 1 0 0 ^ 2 * a 0 1 1 ^ 2)
    - 2 * (a 0 0 0 * a 1 1 1 * a 0 1 1 * a 1 0 0 + a 0 0 0 * a 1 1 1 * a 1 0 1 * a 0 1 0
      + a 0 0 0 * a 1 1 1 * a 1 1 0 * a 0 0 1 + a 0 1 1 * a 1 0 0 * a 1 0 1 * a 0 1 0
      + a 0 1 1 * a 1 0 0 * a 1 1 0 * a 0 0 1 + a 1 0 1 * a 0 1 0 * a 1 1 0 * a 0 0 1)
    + 4 * (a 0 0 0 * a 1 1 0 * a 1 0 1 * a 0 1 1 + a 1 1 1 * a 0 0 1 * a 0 1 0 * a 1 0 0)

/-- The three-tangle `τ_ABC = 4 |Det ψ|` (CKW 2000). -/
noncomputable def threeTangle : ℝ := 4 * ‖hyperdet ψ‖

theorem reduceAC_eq : reduceAC ψ = vAC ψ * (vAC ψ)ᴴ := by
  ext p q; simp [reduceAC, vAC, Matrix.mul_apply, conjTranspose_apply]

theorem det_tMat_AB : (tMat ψ).det = -hyperdet ψ := by
  rw [det_fin_two, tMat_apply, tMat_apply, tMat_apply, tMat_apply, hyperdet]
  ring

theorem det_tMat_AC : (tMat (vAC ψ)).det = -hyperdet ψ := by
  rw [det_fin_two, tMat_apply, tMat_apply, tMat_apply, tMat_apply, hyperdet]
  simp only [vAC]
  ring

theorem frob_complex (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (frob T : ℂ) = T 0 0 * conj (T 0 0) + T 0 1 * conj (T 0 1) + (T 1 0 * conj (T 1 0)
      + T 1 1 * conj (T 1 1)) := by
  simp only [frob, Fin.sum_univ_two, Complex.ofReal_add, Complex.mul_conj]

/-- The polynomial identity behind CKW: `‖T_AB‖²_F + ‖T_AC‖²_F = 4 det ρ_A`. -/
theorem frob_add_frob : ((frob (tMat ψ) + frob (tMat (vAC ψ)) : ℝ) : ℂ) = 4 * (rhoA ψ).det := by
  rw [Complex.ofReal_add, frob_complex, frob_complex]
  simp only [tMat_apply, vAC, rhoA, selfState, splitA, det_fin_two, Matrix.mul_apply,
    conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two, map_add, map_sub, map_neg,
    map_mul, RCLike.star_def]
  ring

/-- **The CKW identity for three qubits.** For every pure state `ψ` of qubits A, B, C (no
normalisation needed), `C(ρ_AB)² + C(ρ_AC)² + τ_ABC = τ_{A|BC}`, with `C` Wootters' concurrence,
`τ_ABC = 4 |Det ψ|` the three-tangle and `τ_{A|BC} = 4 det ρ_A`. -/
theorem ckw_identity :
    concurrence (selfState ψ) ^ 2 + concurrence (reduceAC ψ) ^ 2 + threeTangle ψ = tangleA ψ := by
  have hAB : concurrence (selfState ψ) ^ 2 = frob (tMat ψ) - 2 * ‖hyperdet ψ‖ := by
    rw [selfState, concurrence_sq_rankTwo, det_tMat_AB, norm_neg]
  have hAC : concurrence (reduceAC ψ) ^ 2 = frob (tMat (vAC ψ)) - 2 * ‖hyperdet ψ‖ := by
    rw [reduceAC_eq, concurrence_sq_rankTwo, det_tMat_AC, norm_neg]
  have hF : frob (tMat ψ) + frob (tMat (vAC ψ)) = tangleA ψ := by
    have := congrArg Complex.re (frob_add_frob ψ)
    rw [Complex.ofReal_re] at this
    rw [this, tangleA]; simp
  rw [hAB, hAC, threeTangle, ← hF]; ring

/-- **Coffman–Kundu–Wootters monogamy for three qubits.** For every pure state of three qubits,
`τ_AB + τ_AC ≤ τ_{A|BC}`, with `τ_AB = C(ρ_AB)²` (Wootters' concurrence, squared) and
`τ_{A|BC} = 4 det ρ_A`. -/
theorem ckw : concurrence (selfState ψ) ^ 2 + concurrence (reduceAC ψ) ^ 2 ≤ tangleA ψ := by
  rw [← ckw_identity ψ]
  have : 0 ≤ threeTangle ψ := by unfold threeTangle; positivity
  linarith

/-- Equality in CKW exactly when the hyperdeterminant vanishes (e.g. the W class). -/
theorem ckw_eq_iff :
    concurrence (selfState ψ) ^ 2 + concurrence (reduceAC ψ) ^ 2 = tangleA ψ ↔ hyperdet ψ = 0 := by
  rw [← ckw_identity ψ, threeTangle]
  constructor
  · intro h; exact norm_eq_zero.1 (by linarith)
  · intro h; rw [h, norm_zero]; ring

end ThreeQubits

end PEqualNP.QuantumGravity.Open.CKW
