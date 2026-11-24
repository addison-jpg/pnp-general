import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-149: the distance of the five-qubit code is not four. Some Pauli operator that commutes
with the five-qubit stabilizer group and is not in it acts on only three qubits (`IYYIX` is
one), so with L-qg-140 the distance is exactly three. -/

theorem PEqualNP.QuantumGravity.L149 :
    ¬ PEqualNP.QuantumGravity.HasDistance PEqualNP.QuantumGravity.fiveQubitCode 4 :=
  PEqualNP.QuantumGravity.Helpers.not_hasDistance_fiveQubitCode_four
