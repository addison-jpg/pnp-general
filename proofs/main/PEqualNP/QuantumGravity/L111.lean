import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-111: errors add. If `U` is within `ε` of a product of at most `k` gates and `W` within
`δ` of a product of at most `m` gates, in the operator norm, then `U * W` is within `ε + δ` of a
product of at most `k + m` gates. The approximate form of L-qg-003 (Knill 1995, Lemma 2.3). -/

theorem PEqualNP.QuantumGravity.L111 : PEqualNP.QuantumGravity.Gap.L111 :=
  fun _ _ _ _ _ _ _ _ _ _ hU hW => PEqualNP.QuantumGravity.Helpers.mul_mem_approx hU hW
