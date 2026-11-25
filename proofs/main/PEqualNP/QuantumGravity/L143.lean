import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-143: the six-qubit perfect stabilizer group is Lagrangian. A Pauli operator on six
qubits commutes with every element of the group exactly when it is in the group: the group is
its own symplectic complement. So it fixes a single state of the six qubits, with no logical
qubit left over. -/

theorem PEqualNP.QuantumGravity.L143 :
    PEqualNP.QuantumGravity.pauliNormalizer PEqualNP.QuantumGravity.sixQubitPerfect =
      (PEqualNP.QuantumGravity.sixQubitPerfect :
        Set (PEqualNP.QuantumGravity.PauliVec 6)) :=
  PEqualNP.QuantumGravity.Helpers.pauliNormalizer_sixQubitPerfect
