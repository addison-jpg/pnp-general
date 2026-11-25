import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-162: NP is inside P_CTC (Brun; Aaronson and Watrous). The register on the closed
timelike curve has one bit more than the witness bound; it stands for the witness left after its
leading `false` bits and first `true` bit. The circuit keeps the register when the verifier
accepts that witness and otherwise adds one to the register, read as a binary number. When a
witness exists, every Deutsch-consistent distribution charges only accepted witnesses (row
L-qg-166); when none exists, no register is accepted. -/

theorem PEqualNP.QuantumGravity.L162 :
    PEqualNP.Library.NP ⊆ PEqualNP.QuantumGravity.PCTC :=
  PEqualNP.QuantumGravity.Helpers.NP_subset_PCTC
