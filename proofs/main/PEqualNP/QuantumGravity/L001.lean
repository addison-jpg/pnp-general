import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-001: at most `(|S| + 1)^k` elements of a monoid are products of at most `k` gates from a
finite gate set `S`. This is the counting step behind "most unitaries have exponential
complexity" in the holographic complexity literature, in its classical form. -/

theorem PEqualNP.QuantumGravity.L001 :
    ∀ (G : Type) [Monoid G] (S : Finset G) (k : ℕ),
      (PEqualNP.QuantumGravity.ReachableIn (S : Set G) k).ncard ≤ (S.card + 1) ^ k :=
  fun _ _ S k => PEqualNP.QuantumGravity.Helpers.ncard_reachableIn_le S k
