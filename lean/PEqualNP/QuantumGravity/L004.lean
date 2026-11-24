import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-004: complexity grows at most linearly in time. If one step `g` of a time evolution has a
circuit of at most `k` gates, then `t` steps, `g ^ t`, have one of at most `t * k` gates. This is
the upper half of the linear growth in Brown and Susskind's second law of quantum complexity. -/

theorem PEqualNP.QuantumGravity.L004 :
    ∀ (G : Type) [Monoid G] (S : Set G) (k : ℕ) (g : G),
      g ∈ PEqualNP.QuantumGravity.ReachableIn S k →
        ∀ t : ℕ, g ^ t ∈ PEqualNP.QuantumGravity.ReachableIn S (t * k) :=
  fun _ _ _ _ _ hg t => PEqualNP.QuantumGravity.Helpers.pow_mem_reachableIn hg t
