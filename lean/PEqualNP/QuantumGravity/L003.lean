import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-003: circuit complexity is subadditive. If `g` has a circuit of at most `k` gates and `h`
one of at most `m` gates, then `g * h` has one of at most `k + m` gates. -/

theorem PEqualNP.QuantumGravity.L003 :
    ∀ (G : Type) [Monoid G] (S : Set G) (k m : ℕ) (g h : G),
      g ∈ PEqualNP.QuantumGravity.ReachableIn S k →
        h ∈ PEqualNP.QuantumGravity.ReachableIn S m →
          g * h ∈ PEqualNP.QuantumGravity.ReachableIn S (k + m) :=
  fun _ _ _ _ _ _ _ hg hh => PEqualNP.QuantumGravity.Helpers.mul_mem_reachableIn hg hh
