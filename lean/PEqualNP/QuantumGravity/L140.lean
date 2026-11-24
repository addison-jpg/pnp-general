import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-140: the five-qubit code is a stabilizer code of distance three. Its generators `XZZXI`,
`IXZZX`, `XIXZZ`, `ZXIXZ` span a subspace whose elements commute pairwise, and every Pauli
operator that commutes with all of them and is not in their span acts on at least three qubits.
This is the code `[[5,1,3]]` that the holographic codes of Pastawski, Yoshida, Harlow and
Preskill are built from. -/

theorem PEqualNP.QuantumGravity.L140 :
    PEqualNP.QuantumGravity.IsIsotropic PEqualNP.QuantumGravity.fiveQubitCode ∧
      PEqualNP.QuantumGravity.HasDistance PEqualNP.QuantumGravity.fiveQubitCode 3 :=
  ⟨PEqualNP.QuantumGravity.Helpers.fiveQubitCode_isIsotropic,
    PEqualNP.QuantumGravity.Helpers.fiveQubitCode_hasDistance⟩
