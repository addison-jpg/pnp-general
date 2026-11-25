import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-110: no countable gate set is exactly universal. For every countable gate set `S` of
unitaries of `n` qubits, some unitary of `n` qubits is a product of no finite word of gates from
`S`. The words are countable; the unitary group is not, since the phases `exp (i θ) • 1`
already form an uncountable family. -/

theorem PEqualNP.QuantumGravity.L110 : PEqualNP.QuantumGravity.Gap.L110 :=
  fun _ _ hS => PEqualNP.QuantumGravity.Helpers.exists_not_mem_iUnion_reachableIn hS
