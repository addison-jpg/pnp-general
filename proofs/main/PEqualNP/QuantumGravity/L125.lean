import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-125: the deterministic case of L-qg-121. For every map `f` of the computational basis
`Fin d`, `d > 0`, the channel with Kraus operators `|f x⟩⟨x|` has a fixed diagonal density
matrix: the diagonal of a distribution that `f` carries to itself, which L-qg-008 provides. -/

theorem PEqualNP.QuantumGravity.L125 :
    ∀ (d : ℕ) (f : Fin d → Fin d), 0 < d →
      ∃ ρ : Matrix (Fin d) (Fin d) ℂ, PEqualNP.QuantumGravity.IsDensityMatrix ρ ∧ ρ.IsDiag ∧
        PEqualNP.QuantumGravity.krausMap (PEqualNP.QuantumGravity.krausOfMap f) ρ = ρ :=
  fun _ f hd => PEqualNP.QuantumGravity.Helpers.exists_fixed_krausOfMap hd f
