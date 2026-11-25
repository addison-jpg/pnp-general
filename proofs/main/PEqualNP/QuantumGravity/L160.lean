import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-160: the class P_CTC is never vacuous. For every circuit `next` on the pair (input,
register), every input `x` and every register length `m`, the map that the circuit induces on
the `m`-bit register of the closed timelike curve carries some probability distribution to
itself. So "for every Deutsch-consistent distribution" in the definition of `PCTC` always
ranges over at least one distribution. -/

theorem PEqualNP.QuantumGravity.L160 :
    ∀ (next : List Bool × List Bool → List Bool) (x : List Bool) (m : ℕ),
      ∃ μ : PMF (List.Vector Bool m),
        PEqualNP.QuantumGravity.DeutschConsistent
          (PEqualNP.QuantumGravity.ctcRegisterMap next x m) μ :=
  fun next x m => PEqualNP.QuantumGravity.Helpers.exists_consistent_register next x m
