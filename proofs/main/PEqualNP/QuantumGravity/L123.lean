import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-123: Deutsch's quantum consistency for unital channels. When the Kraus operators `K i` on
`Fin d`, `d > 0`, also satisfy `∑ i, K i * (K i)ᴴ = 1` (for example a single unitary), the
maximally mixed state `(1 / d) • 1` is a density matrix and the channel fixes it. -/

theorem PEqualNP.QuantumGravity.L123 :
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∑ i, K i * (K i).conjTranspose = 1 →
        PEqualNP.QuantumGravity.IsDensityMatrix ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
          PEqualNP.QuantumGravity.krausMap K ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) =
            (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  fun _ _ _ _ hd hU => ⟨PEqualNP.QuantumGravity.Helpers.isDensityMatrix_maximallyMixed hd,
    PEqualNP.QuantumGravity.Helpers.krausMap_maximallyMixed hU⟩
