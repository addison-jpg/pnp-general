import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-005: every prefix of a minimal gate word is a minimal gate word. Along a word of gates
whose product has no shorter circuit, the complexity of the first `t` gates is exactly `t`. -/

theorem PEqualNP.QuantumGravity.L005 :
    ∀ (G : Type) [Monoid G] (S : Set G) (l : List G),
      (∀ x ∈ l, x ∈ S) →
        (∀ m < l.length, l.prod ∉ PEqualNP.QuantumGravity.ReachableIn S m) →
          ∀ t ≤ l.length, ∀ m < t,
            (l.take t).prod ∉ PEqualNP.QuantumGravity.ReachableIn S m :=
  fun _ _ _ _ hS hmin t ht => PEqualNP.QuantumGravity.Helpers.take_minimal hS hmin t ht
