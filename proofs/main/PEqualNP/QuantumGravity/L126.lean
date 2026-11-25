import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-126: gap L-qg-120 implies gap L-qg-121. If every quantum channel on a nonempty register has
a fixed density matrix, then every channel that maps diagonal matrices to diagonal matrices has
a fixed diagonal one. The proof applies L-qg-120 to the channel that first keeps only the
diagonal (Kraus operators `K i * |x⟩⟨x|`): its fixed point is the image of a diagonal matrix,
so it is diagonal, and the channel itself fixes it. -/

theorem PEqualNP.QuantumGravity.L126 :
    (∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
        0 < d → PEqualNP.QuantumGravity.IsKrausFamily K →
          ∃ ρ, PEqualNP.QuantumGravity.IsDensityMatrix ρ ∧
            PEqualNP.QuantumGravity.krausMap K ρ = ρ) →
      ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
        0 < d → PEqualNP.QuantumGravity.IsKrausFamily K →
          PEqualNP.QuantumGravity.MapsDiagonalToDiagonal K →
            ∃ ρ, PEqualNP.QuantumGravity.IsDensityMatrix ρ ∧ ρ.IsDiag ∧
              PEqualNP.QuantumGravity.krausMap K ρ = ρ := by
  intro h120 d ι _ K hd hK hD
  obtain ⟨ρ, hρ, hfix⟩ := h120 d (ι × Fin d) (PEqualNP.QuantumGravity.Helpers.dephasedKraus K) hd
    (PEqualNP.QuantumGravity.Helpers.isKrausFamily_dephasedKraus hK)
  obtain ⟨hdiag, hfix'⟩ := PEqualNP.QuantumGravity.Helpers.exists_fixed_diag_of_exists_fixed hD hfix
  exact ⟨ρ, hρ, hdiag, hfix'⟩
