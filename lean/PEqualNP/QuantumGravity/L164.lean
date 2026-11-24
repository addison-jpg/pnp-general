import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-164: P_CTC is closed under complement. Keep the circuit on the closed timelike curve
and negate the read-out. -/

theorem PEqualNP.QuantumGravity.L164 :
    ∀ L : Language Bool, L ∈ PEqualNP.QuantumGravity.PCTC → Lᶜ ∈ PEqualNP.QuantumGravity.PCTC :=
  fun _ hL => PEqualNP.QuantumGravity.Helpers.PCTC_compl hL
