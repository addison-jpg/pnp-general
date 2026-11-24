import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-113: compiling one gate set into another. If every gate of `T` is within `δ` of a
product of at most `m` gates of `S`, then every unitary within `ε` of a product of at most `k`
gates of `T` is within `ε + k δ` of a product of at most `k m` gates of `S`. -/

theorem PEqualNP.QuantumGravity.L113 : PEqualNP.QuantumGravity.Gap.L113 :=
  fun _ _ _ _ _ _ _ _ _ hδ hT => PEqualNP.QuantumGravity.Helpers.approx_compile hδ hT
