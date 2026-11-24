import PEqualNP.QuantumGravity.Helpers.Channels

/-! L-qg-124: the classical, deterministic register embedded. For every map `f` of the
computational basis `Fin d`, the operators `|f x⟩⟨x|` are the Kraus operators of a channel; the
channel reads the diagonal of `ρ` and pushes it forward along `f`, so it maps every matrix to a
diagonal matrix. -/

theorem PEqualNP.QuantumGravity.L124 :
    ∀ (d : ℕ) (f : Fin d → Fin d),
      PEqualNP.QuantumGravity.IsKrausFamily (PEqualNP.QuantumGravity.krausOfMap f) ∧
        PEqualNP.QuantumGravity.MapsDiagonalToDiagonal (PEqualNP.QuantumGravity.krausOfMap f) ∧
          ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
            PEqualNP.QuantumGravity.krausMap (PEqualNP.QuantumGravity.krausOfMap f) ρ =
              Matrix.diagonal (fun y => ∑ x, if f x = y then ρ x x else 0) :=
  fun _ f => ⟨PEqualNP.QuantumGravity.Helpers.isKrausFamily_krausOfMap f,
    PEqualNP.QuantumGravity.Helpers.mapsDiagonalToDiagonal_krausOfMap f,
    PEqualNP.QuantumGravity.Helpers.krausMap_krausOfMap f⟩
