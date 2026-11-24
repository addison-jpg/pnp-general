import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-142: the five-qubit code recovers from the loss of any two qubits. For every set `E` of
at most two of the five qubits, no Pauli operator that commutes with the stabilizer group and
is not in it acts only on qubits in `E`. This follows from distance three (L-qg-140) and
L-qg-148. -/

theorem PEqualNP.QuantumGravity.L142 :
    ∀ E : Finset (Fin 5), E.card ≤ 2 →
      PEqualNP.QuantumGravity.CorrectsErasure PEqualNP.QuantumGravity.fiveQubitCode E :=
  fun _ hE => PEqualNP.QuantumGravity.Helpers.fiveQubitCode_correctsErasure hE
