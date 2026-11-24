import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-165: coNP is inside P_CTC. The complement of a coNP language is in NP, hence in P_CTC
(row L-qg-162), and P_CTC is closed under complement (row L-qg-164). -/

theorem PEqualNP.QuantumGravity.L165 :
    PEqualNP.Library.coNP ⊆ PEqualNP.QuantumGravity.PCTC :=
  PEqualNP.QuantumGravity.Helpers.coNP_subset_PCTC
