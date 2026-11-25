import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-145: the five-qubit code inside the perfect state, logical operators. A Pauli operator
on five qubits commutes with the five-qubit stabilizer group exactly when it is the first five
qubits of an element of the six-qubit perfect stabilizer group. This is the stabilizer form of
the statement that the perfect tensor, with its sixth leg as input, is the encoding map of the
five-qubit code. -/

theorem PEqualNP.QuantumGravity.L145 :
    ∀ b : PEqualNP.QuantumGravity.PauliVec 5,
      b ∈ PEqualNP.QuantumGravity.pauliNormalizer PEqualNP.QuantumGravity.fiveQubitCode ↔
        ∃ s ∈ PEqualNP.QuantumGravity.sixQubitPerfect,
          b = (fun i => s.1 (Fin.castSucc i), fun i => s.2 (Fin.castSucc i)) :=
  PEqualNP.QuantumGravity.Helpers.mem_pauliNormalizer_fiveQubitCode_iff
