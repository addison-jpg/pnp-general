import PEqualNP.QuantumGravity.Helpers.Ctc

/-! L-qg-009: a closed timelike curve finds solutions. For the search map on the register
`ZMod N` (keep `x` when `φ x`, else step to `x + 1`), if some point satisfies `φ`, every
Deutsch-consistent distribution charges only points that satisfy `φ`. With `N = 2^n` and `φ` a
formula on `n` variables, this is the core of Brun's and Aaronson and Watrous's argument that a
closed timelike curve decides satisfiability with one pass of a polynomial-size circuit. -/

theorem PEqualNP.QuantumGravity.L009 :
    ∀ (N : ℕ) [NeZero N] (φ : ZMod N → Bool), (∃ s, φ s = true) →
      ∀ μ : PMF (ZMod N), PEqualNP.QuantumGravity.DeutschConsistent
          (PEqualNP.QuantumGravity.ctcSearchMap φ) μ →
        ∀ y ∈ μ.support, φ y = true :=
  fun _ _ _ hs _ hμ _ hy => PEqualNP.QuantumGravity.Helpers.consistent_support_sat hs hμ hy
