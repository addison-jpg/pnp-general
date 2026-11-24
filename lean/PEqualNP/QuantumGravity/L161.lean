import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-161: P is inside P_CTC. A language decided in polynomial time is decided with a closed
timelike curve: read the answer from the input alone and leave the register empty. -/

theorem PEqualNP.QuantumGravity.L161 :
    PEqualNP.Library.P ⊆ PEqualNP.QuantumGravity.PCTC :=
  PEqualNP.QuantumGravity.Helpers.P_subset_PCTC
