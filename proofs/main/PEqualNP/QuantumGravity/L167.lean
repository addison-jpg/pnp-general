import PEqualNP.QuantumGravity.Helpers.CtcClass

/-! L-qg-167: after as many steps as there are states, every orbit sits on a cycle. For every map
`f` of a finite set and every point `x`, the point reached from `x` after as many steps as the set
has elements is charged by some Deutsch-consistent distribution of `f` (the uniform distribution
on its cycle). This is the step of Aaronson and Watrous's simulation of a closed timelike curve
in PSPACE: run the circuit `2^m` times from any register and read the answer there. -/

theorem PEqualNP.QuantumGravity.L167 :
    ∀ (S : Type) [Fintype S] (f : S → S) (x : S),
      ∃ μ : PMF S, PEqualNP.QuantumGravity.DeutschConsistent f μ ∧
        f^[Fintype.card S] x ∈ μ.support :=
  fun _ _ f x => PEqualNP.QuantumGravity.Helpers.consistent_mem_iterate_card f x
