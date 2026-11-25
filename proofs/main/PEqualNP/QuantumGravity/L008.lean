import PEqualNP.QuantumGravity.Helpers.Ctc

/-! L-qg-008: Deutsch's causal consistency condition always has a solution for a classical
register: every map of a nonempty finite set carries some probability distribution on it to
itself. -/

theorem PEqualNP.QuantumGravity.L008 :
    ∀ (S : Type) [Finite S] [Nonempty S] (f : S → S),
      ∃ μ : PMF S, PEqualNP.QuantumGravity.DeutschConsistent f μ :=
  fun _ _ _ f => PEqualNP.QuantumGravity.Helpers.exists_consistent f
