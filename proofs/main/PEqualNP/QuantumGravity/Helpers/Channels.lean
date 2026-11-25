import PEqualNP.Defs.QuantumGravityChannels
import PEqualNP.QuantumGravity.Helpers.Ctc

/-!
Helpers for L-qg-122 to L-qg-127: quantum channels in Kraus form map density matrices to
density matrices; unital channels fix the maximally mixed state; the embedding of a map of the
computational basis as a channel, and its fixed diagonal density matrix (from L-qg-008); the
reduction of the classical case of Deutsch's quantum consistency (L-qg-121) to the quantum case
(L-qg-120), by composing with the channel that keeps only the diagonal; and its reduction to
stationary distributions of Markov kernels (L-qg-102), through the stochastic matrix of the
channel on the diagonal.
-/

namespace PEqualNP.QuantumGravity.Helpers

open Matrix
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] {d : ℕ}

section Kraus

theorem trace_krausMap {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : (krausMap K ρ).trace = ρ.trace := by
  unfold krausMap
  rw [trace_sum]
  simp_rw [trace_mul_cycle (K _) ρ]
  rw [← trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

theorem posSemidef_krausMap (K : ι → Matrix (Fin d) (Fin d) ℂ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (krausMap K ρ).PosSemidef :=
  posSemidef_sum _ fun i _ => hρ.mul_mul_conjTranspose_same (K i)

/-- A channel in Kraus form maps density matrices to density matrices. -/
theorem isDensityMatrix_krausMap {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) : IsDensityMatrix (krausMap K ρ) :=
  ⟨posSemidef_krausMap K hρ.1, (trace_krausMap hK ρ).trans hρ.2⟩

theorem krausMap_smul (K : ι → Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    krausMap K (c • ρ) = c • krausMap K ρ := by
  simp only [krausMap, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

/-- The maximally mixed state `(1 / d) • 1` is a density matrix. -/
theorem isDensityMatrix_maximallyMixed (hd : 0 < d) :
    IsDensityMatrix ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  refine ⟨PosSemidef.one.smul ?_, ?_⟩
  · rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg d))
  · rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne')

/-- A unital Kraus map fixes the maximally mixed state. -/
theorem krausMap_maximallyMixed {K : ι → Matrix (Fin d) (Fin d) ℂ}
    (hU : ∑ i, K i * (K i)ᴴ = 1) :
    krausMap K ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) = (d : ℂ)⁻¹ • 1 := by
  rw [krausMap_smul]
  simp only [krausMap, Matrix.mul_one, hU]

end Kraus

section Classical

/-- The channel of a map `f` of the computational basis reads the diagonal of `ρ` and pushes it
forward along `f`. -/
theorem krausMap_krausOfMap (f : Fin d → Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    krausMap (krausOfMap f) ρ =
      diagonal (fun y => ∑ x, if f x = y then ρ x x else 0) := by
  unfold krausMap krausOfMap
  simp only [conjTranspose_single, star_one, single_mul_mul_single, one_mul, mul_one]
  ext a b
  rw [Matrix.sum_apply, diagonal_apply]
  split_ifs with hab
  · subst hab
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : f x = a <;> simp [hx]
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [single_apply, ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exact absurd rfl hab

theorem isKrausFamily_krausOfMap (f : Fin d → Fin d) : IsKrausFamily (krausOfMap f) := by
  unfold IsKrausFamily krausOfMap
  simp only [conjTranspose_single, star_one, single_mul_single_same, mul_one]
  exact sum_single_one

theorem mapsDiagonalToDiagonal_krausOfMap (f : Fin d → Fin d) :
    MapsDiagonalToDiagonal (krausOfMap f) := fun ρ _ => by
  rw [krausMap_krausOfMap]
  exact isDiag_diagonal _

/-- The diagonal density matrix with the distribution `μ` on its diagonal. -/
noncomputable def diagonalOfPMF (μ : PMF (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal (fun x => (((μ x).toReal : ℝ) : ℂ))

theorem isDensityMatrix_diagonalOfPMF (μ : PMF (Fin d)) :
    IsDensityMatrix (diagonalOfPMF μ) := by
  refine ⟨PosSemidef.diagonal fun x => Complex.zero_le_real.mpr ENNReal.toReal_nonneg, ?_⟩
  have h1 : ∑ x, μ x = 1 := (tsum_fintype (L := .unconditional _) _).symm.trans μ.tsum_coe
  rw [diagonalOfPMF, trace_diagonal, ← Complex.ofReal_sum,
    ← ENNReal.toReal_sum fun x _ => PMF.apply_ne_top μ x, h1]
  simp

/-- The channel of a map `f` of the computational basis fixes the diagonal density matrix of
every distribution that `f` carries to itself. -/
theorem krausMap_krausOfMap_diagonalOfPMF (f : Fin d → Fin d) {μ : PMF (Fin d)}
    (hμ : DeutschConsistent f μ) :
    krausMap (krausOfMap f) (diagonalOfPMF μ) = diagonalOfPMF μ := by
  rw [krausMap_krausOfMap]
  conv_rhs => rw [diagonalOfPMF, ← hμ]
  congr 1
  funext y
  rw [PMF.map_apply, tsum_fintype (L := .unconditional _), ENNReal.toReal_sum fun x _ => by
    split_ifs
    · exact PMF.apply_ne_top μ x
    · exact ENNReal.zero_ne_top, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [diagonalOfPMF, diagonal_apply_eq, eq_comm (a := y)]
  split_ifs <;> simp

/-- Every map of a nonempty computational basis, embedded as a channel, has a fixed diagonal
density matrix. -/
theorem exists_fixed_krausOfMap (hd : 0 < d) (f : Fin d → Fin d) :
    ∃ ρ, IsDensityMatrix ρ ∧ ρ.IsDiag ∧ krausMap (krausOfMap f) ρ = ρ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨μ, hμ⟩ := exists_consistent f
  exact ⟨diagonalOfPMF μ, isDensityMatrix_diagonalOfPMF μ, isDiag_diagonal _,
    krausMap_krausOfMap_diagonalOfPMF f hμ⟩

end Classical

section Dephasing

/-- The dephasing channel `ρ ↦ diagonal (diag ρ)` followed by the channel `krausMap K`: its
Kraus operators are `K i * |x⟩⟨x|`. -/
def dephasedKraus (K : ι → Matrix (Fin d) (Fin d) ℂ) (p : ι × Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  K p.1 * single p.2 p.2 1

theorem isKrausFamily_dephasedKraus {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K) :
    IsKrausFamily (dephasedKraus K) := by
  unfold IsKrausFamily dephasedKraus
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [conjTranspose_mul, conjTranspose_single, star_one]
  have h : ∀ x : Fin d, ∑ i, single x x (1 : ℂ) * (K i)ᴴ * (K i * single x x 1) =
      single x x 1 := by
    intro x
    calc ∑ i, single x x (1 : ℂ) * (K i)ᴴ * (K i * single x x 1)
        = single x x 1 * (∑ i, (K i)ᴴ * K i) * single x x 1 := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.mul_assoc]
      _ = single x x 1 := by rw [hK, Matrix.mul_one, single_mul_single_same, mul_one]
  simp only [h]
  exact sum_single_one

theorem krausMap_dephasedKraus (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    krausMap (dephasedKraus K) ρ = krausMap K (diagonal (diag ρ)) := by
  unfold krausMap dephasedKraus
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [conjTranspose_mul, conjTranspose_single, star_one]
  have h : ∀ x : Fin d, K i * single x x 1 * ρ * (single x x 1 * (K i)ᴴ) =
      K i * single x x (ρ x x) * (K i)ᴴ := by
    intro x
    calc K i * single x x 1 * ρ * (single x x 1 * (K i)ᴴ)
        = K i * (single x x 1 * ρ * single x x 1) * (K i)ᴴ := by simp only [Matrix.mul_assoc]
      _ = K i * single x x (ρ x x) * (K i)ᴴ := by rw [single_mul_mul_single, one_mul, mul_one]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_eq_diagonal]
  rfl

/-- The classical case of Deutsch's quantum consistency follows from the quantum case: a
fixed density matrix of the dephased channel is diagonal and is fixed by the channel. -/
theorem exists_fixed_diag_of_exists_fixed {K : ι → Matrix (Fin d) (Fin d) ℂ}
    (hD : MapsDiagonalToDiagonal K) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : krausMap (dephasedKraus K) ρ = ρ) : ρ.IsDiag ∧ krausMap K ρ = ρ := by
  rw [krausMap_dephasedKraus] at hρ
  have hdiag : ρ.IsDiag := hρ ▸ hD _ (isDiag_diagonal _)
  refine ⟨hdiag, ?_⟩
  rwa [hdiag.diagonal_diag] at hρ

end Dephasing

section Stochastic

theorem krausMap_sum (K : ι → Matrix (Fin d) (Fin d) ℂ) {κ : Type} [Fintype κ]
    (A : κ → Matrix (Fin d) (Fin d) ℂ) : krausMap K (∑ x, A x) = ∑ x, krausMap K (A x) := by
  unfold krausMap
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem isDiag_single (x : Fin d) : (single x x (1 : ℂ)).IsDiag := fun _ _ hij =>
  single_apply_of_ne _ _ _ _ _ fun h => hij (h.1.symm.trans h.2)

theorem isDensityMatrix_single (x : Fin d) : IsDensityMatrix (single x x (1 : ℂ)) := by
  refine ⟨?_, trace_single_eq_same x 1⟩
  simpa using (PosSemidef.one (n := Fin d) (R := ℂ)).mul_mul_conjTranspose_same (single x x 1)

/-- On the diagonal of a density matrix stand nonnegative real numbers. -/
theorem diag_of_isDensityMatrix {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ)
    (y : Fin d) : 0 ≤ (ρ y y).re ∧ ρ y y = ((ρ y y).re : ℂ) := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hρ.1.diag_nonneg (i := y))
  exact ⟨hre, Complex.ext rfl (by simpa using him.symm)⟩

theorem sum_diag_re_of_isDensityMatrix {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) :
    ∑ y, (ρ y y).re = 1 := by
  rw [← Complex.re_sum]
  have h := hρ.2
  rw [Matrix.trace] at h
  simp only [diag_apply] at h
  rw [h, Complex.one_re]

/-- The stochastic matrix of a channel on the diagonal: from the basis state `x`, the
distribution on the diagonal of the image of `|x⟩⟨x|`. -/
noncomputable def diagonalKernel {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K)
    (x : Fin d) : PMF (Fin d) :=
  PMF.ofFintype (fun y => ENNReal.ofReal (krausMap K (single x x 1) y y).re) (by
    have hσ := isDensityMatrix_krausMap hK (isDensityMatrix_single x)
    rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => (diag_of_isDensityMatrix hσ y).1,
      sum_diag_re_of_isDensityMatrix hσ, ENNReal.ofReal_one])

theorem diagonalOfPMF_eq_sum (μ : PMF (Fin d)) :
    diagonalOfPMF μ = ∑ x, (((μ x).toReal : ℝ) : ℂ) • single x x (1 : ℂ) := by
  rw [diagonalOfPMF, ← sum_single_eq_diagonal]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_single, smul_eq_mul, mul_one]

/-- A channel that maps diagonal matrices to diagonal matrices fixes the diagonal density
matrix of every stationary distribution of its stochastic matrix. -/
theorem krausMap_diagonalOfPMF_of_stationary {K : ι → Matrix (Fin d) (Fin d) ℂ}
    (hK : IsKrausFamily K) (hD : MapsDiagonalToDiagonal K) {μ : PMF (Fin d)}
    (hμ : μ.bind (diagonalKernel hK) = μ) : krausMap K (diagonalOfPMF μ) = diagonalOfPMF μ := by
  have hσ : ∀ x, IsDensityMatrix (krausMap K (single x x 1)) := fun x =>
    isDensityMatrix_krausMap hK (isDensityMatrix_single x)
  rw [diagonalOfPMF_eq_sum, krausMap_sum]
  simp only [krausMap_smul]
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← diagonalOfPMF_eq_sum, diagonalOfPMF, diagonal_apply]
  split_ifs with hab
  · subst hab
    have hreal : ∑ x, (μ x).toReal * (krausMap K (single x x 1) a a).re = (μ a).toReal := by
      conv_rhs => rw [← hμ, PMF.bind_apply, tsum_fintype (L := .unconditional _)]
      rw [ENNReal.toReal_sum fun x _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ENNReal.toReal_mul, diagonalKernel, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (diag_of_isDensityMatrix (hσ x) a).1]
    rw [← hreal, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.ofReal_mul, ← (diag_of_isDensityMatrix (hσ x) a).2]
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [hD _ (isDiag_single x) hab, mul_zero]

/-- If every Markov kernel on a nonempty finite register has a stationary distribution, every
channel that maps diagonal matrices to diagonal matrices has a fixed diagonal density matrix. -/
theorem exists_fixed_diag_of_stationary
    (h102 : ∀ (S : Type) [Fintype S] [Nonempty S] (P : S → PMF S), ∃ μ : PMF S, μ.bind P = μ)
    (hd : 0 < d) {K : ι → Matrix (Fin d) (Fin d) ℂ} (hK : IsKrausFamily K)
    (hD : MapsDiagonalToDiagonal K) :
    ∃ ρ, IsDensityMatrix ρ ∧ ρ.IsDiag ∧ krausMap K ρ = ρ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨μ, hμ⟩ := h102 (Fin d) (diagonalKernel hK)
  exact ⟨diagonalOfPMF μ, isDensityMatrix_diagonalOfPMF μ, isDiag_diagonal _,
    krausMap_diagonalOfPMF_of_stationary hK hD hμ⟩

end Stochastic

end PEqualNP.QuantumGravity.Helpers
