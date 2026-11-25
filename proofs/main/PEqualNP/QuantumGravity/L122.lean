import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-122: a quantum channel in Kraus form maps density matrices to density matrices. For Kraus
operators `K i` on `Fin d` with `∑ i, (K i)ᴴ * K i = 1`, the matrix `∑ i, K i * ρ * (K i)ᴴ` is
positive semidefinite and has trace 1 whenever `ρ` is. -/

theorem PEqualNP.QuantumGravity.L122 :
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
      PEqualNP.QuantumGravity.IsKrausFamily K →
        ∀ ρ : Matrix (Fin d) (Fin d) ℂ, PEqualNP.QuantumGravity.IsDensityMatrix ρ →
          PEqualNP.QuantumGravity.IsDensityMatrix (PEqualNP.QuantumGravity.krausMap K ρ) :=
  fun _ _ _ _ hK _ hρ => PEqualNP.QuantumGravity.Helpers.isDensityMatrix_krausMap hK hρ
