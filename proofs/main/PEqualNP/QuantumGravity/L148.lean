import PEqualNP.QuantumGravity.Helpers.Codes

/-! L-qg-148: a stabilizer code of distance `d` recovers from the loss of any set of fewer than
`d` qubits: no Pauli operator that commutes with the stabilizer group and is not in it acts only
on the lost qubits. -/

theorem PEqualNP.QuantumGravity.L148 :
    ∀ (n : ℕ) (S : Submodule (ZMod 2) (PEqualNP.QuantumGravity.PauliVec n)) (d : ℕ)
      (E : Finset (Fin n)), PEqualNP.QuantumGravity.HasDistance S d → E.card < d →
        PEqualNP.QuantumGravity.CorrectsErasure S E :=
  fun _ _ _ _ hS hE => PEqualNP.QuantumGravity.Helpers.correctsErasure_of_hasDistance hS hE
