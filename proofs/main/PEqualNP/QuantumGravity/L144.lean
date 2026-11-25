import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-144: the five-qubit code inside the perfect state, stabilizers. A Pauli operator on five
qubits is in the five-qubit stabilizer group exactly when it is the first five qubits of an
element of the six-qubit perfect stabilizer group that is the identity on the sixth qubit. -/

theorem PEqualNP.QuantumGravity.L144 :
    ∀ a : PEqualNP.QuantumGravity.PauliVec 5,
      a ∈ PEqualNP.QuantumGravity.fiveQubitCode ↔
        ∃ s ∈ PEqualNP.QuantumGravity.sixQubitPerfect,
          s.1 (Fin.last 5) = 0 ∧ s.2 (Fin.last 5) = 0 ∧
            a = (fun i => s.1 (Fin.castSucc i), fun i => s.2 (Fin.castSucc i)) :=
  PEqualNP.QuantumGravity.Helpers.mem_fiveQubitCode_iff_restrict
