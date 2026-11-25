import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-141: the six-qubit perfect state. Its generators `XZZXII`, `IXZZXI`, `XIXZZI`, `ZXIXZI`,
`XXXXXX`, `ZZZZZZ` span a subspace whose elements commute pairwise, and every element of that
subspace other than the identity acts on at least four of the six qubits. In stabilizer language
this says that no stabilizer is supported on three qubits or fewer, which is the perfect tensor
property of the holographic codes. -/

theorem PEqualNP.QuantumGravity.L141 :
    PEqualNP.QuantumGravity.IsIsotropic PEqualNP.QuantumGravity.sixQubitPerfect ∧
      ∀ a ∈ PEqualNP.QuantumGravity.sixQubitPerfect, a ≠ 0 →
        4 ≤ PEqualNP.QuantumGravity.pauliWeight a :=
  ⟨PEqualNP.QuantumGravity.Helpers.sixQubitPerfect_isIsotropic,
    fun _ ha h0 => PEqualNP.QuantumGravity.Helpers.four_le_pauliWeight_of_mem_sixQubitPerfect ha h0⟩
