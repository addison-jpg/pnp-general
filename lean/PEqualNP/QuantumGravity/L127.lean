import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-127: gap L-qg-102 implies gap L-qg-121. If every Markov kernel on a nonempty finite
register has a stationary distribution, then every channel that maps diagonal matrices to
diagonal matrices has a fixed diagonal density matrix. The proof applies L-qg-102 to the
stochastic matrix of the channel on the diagonal: from `x`, the diagonal of the image of
`|x⟩⟨x|`. -/

theorem PEqualNP.QuantumGravity.L127 :
    (∀ (S : Type) [Fintype S] [Nonempty S] (P : S → PMF S), ∃ μ : PMF S, μ.bind P = μ) →
      ∀ (d : ℕ) (ι : Type) [Fintype ι] (K : ι → Matrix (Fin d) (Fin d) ℂ),
        0 < d → PEqualNP.QuantumGravity.IsKrausFamily K →
          PEqualNP.QuantumGravity.MapsDiagonalToDiagonal K →
            ∃ ρ, PEqualNP.QuantumGravity.IsDensityMatrix ρ ∧ ρ.IsDiag ∧
              PEqualNP.QuantumGravity.krausMap K ρ = ρ :=
  fun h102 _ _ _ _ hd hK hD =>
    PEqualNP.QuantumGravity.Helpers.exists_fixed_diag_of_stationary h102 hd hK hD
