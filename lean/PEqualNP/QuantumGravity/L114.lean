import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-114: reversible circuits are quantum circuits. A reversible map `g` of the basis states
has a circuit of at most `k` gates from `S` exactly when the permutation unitary of `g` is a
product of at most `k` permutation unitaries of gates from `S`. Exact quantum complexity over
permutation gates is classical reversible complexity. -/

theorem PEqualNP.QuantumGravity.L114 : PEqualNP.QuantumGravity.Gap.L114 :=
  fun _ _ _ S k g => PEqualNP.QuantumGravity.Helpers.mem_reachableIn_permUnitary_iff S k g
