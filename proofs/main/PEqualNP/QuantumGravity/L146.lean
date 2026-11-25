import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-146: operator pushing through the perfect tensor. For every set `A` of three of the six
qubits and every Pauli operator `p`, exactly one element of the six-qubit perfect stabilizer
group agrees with `p` on the qubits in `A`. So every Pauli operator on three legs of the perfect
tensor can be pushed, in exactly one way, to the other three legs: the stabilizer form of the
statement that every split of the six legs into three and three is unitary. -/

theorem PEqualNP.QuantumGravity.L146 :
    ∀ A : Finset (Fin 6), A.card = 3 → ∀ p : PEqualNP.QuantumGravity.PauliVec 6,
      ∃! s, s ∈ PEqualNP.QuantumGravity.sixQubitPerfect ∧
        ∀ i ∈ A, s.1 i = p.1 i ∧ s.2 i = p.2 i :=
  PEqualNP.QuantumGravity.Helpers.existsUnique_sixQubitPerfect_restrict
