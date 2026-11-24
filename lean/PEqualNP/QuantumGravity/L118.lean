import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-118: the quantum counting bound (gap L-qg-116) gives a hard unitary. If it holds with
constant `C`, then with `c = 1 / C`: whenever `(|S| + 1)^k < (c / ε)^(4^n)`, some unitary of `n`
qubits is not within `ε` of any product of at most `k` gates from `S`. The proof builds the Haar
probability measure (the unitary group is compact) and compares its total mass `1` with the
bound. This is the quantum form of L-qg-002. -/

theorem PEqualNP.QuantumGravity.L118 : PEqualNP.QuantumGravity.Gap.L118 :=
  PEqualNP.QuantumGravity.Helpers.hard_of_knill
