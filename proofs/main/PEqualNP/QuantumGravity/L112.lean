import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-112: approximate complexity grows at most linearly in time. If one step `U` is within
`ε` of a product of at most `k` gates, then `U ^ t` is within `t ε` of a product of at most
`t k` gates. The approximate form of L-qg-004. -/

theorem PEqualNP.QuantumGravity.L112 : PEqualNP.QuantumGravity.Gap.L112 :=
  fun _ _ _ _ _ _ _ hU t => PEqualNP.QuantumGravity.Helpers.pow_mem_approx hU t
