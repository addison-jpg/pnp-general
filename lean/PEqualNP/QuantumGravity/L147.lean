import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-147: the counts. The five-qubit stabilizer group has 16 elements (four independent
generators) and its normalizer has 64, so the code keeps one logical qubit (`64 / 16 = 4`); the
six-qubit perfect stabilizer group has 64 elements (six independent generators on six qubits). -/

theorem PEqualNP.QuantumGravity.L147 :
    (PEqualNP.QuantumGravity.fiveQubitCode :
        Set (PEqualNP.QuantumGravity.PauliVec 5)).ncard = 16 ∧
      (PEqualNP.QuantumGravity.pauliNormalizer PEqualNP.QuantumGravity.fiveQubitCode).ncard = 64 ∧
        (PEqualNP.QuantumGravity.sixQubitPerfect :
          Set (PEqualNP.QuantumGravity.PauliVec 6)).ncard = 64 :=
  ⟨PEqualNP.QuantumGravity.Helpers.ncard_fiveQubitCode,
    PEqualNP.QuantumGravity.Helpers.ncard_pauliNormalizer_fiveQubitCode,
    PEqualNP.QuantumGravity.Helpers.ncard_sixQubitPerfect⟩
