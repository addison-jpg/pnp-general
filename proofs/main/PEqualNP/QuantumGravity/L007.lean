import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-007: recurrence. In a finite group every time evolution `g` returns to the identity
within `|G|` steps, so the complexity of `g ^ t` returns to zero. For the reversible maps of `n`
bits, `|G| = (2^n)!`, a doubly exponential time, as in the quantum recurrence of complexity. -/

theorem PEqualNP.QuantumGravity.L007 :
    ∀ (G : Type) [Group G] [Finite G] (g : G), ∃ t : ℕ, 0 < t ∧ t ≤ Nat.card G ∧ g ^ t = 1 :=
  fun _ _ _ g => ⟨orderOf g, orderOf_pos g, orderOf_le_card, pow_orderOf_eq_one g⟩
