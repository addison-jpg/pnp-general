import PEqualNP.QuantumGravity.Gaps
import PEqualNP.QuantumGravity.Helpers.Stationary

/-! L-qg-102: Deutsch consistency for a probabilistic classical register. Every Markov kernel on
a nonempty finite register has a stationary distribution: some `μ` with `μ.bind K = μ`. This is
the classical half of Aaronson and Watrous's closed timelike curve model, where the circuit on
the curve may flip coins; L-qg-008 is the deterministic case. The proof is linear algebra: the
transition matrix minus the identity is singular, some nonzero row vector lies in the kernel of
its transpose, and the entrywise absolute value of that vector, divided by its sum, is the
stationary distribution. -/

theorem PEqualNP.QuantumGravity.L102 : PEqualNP.QuantumGravity.Gap.L102 :=
  fun _ _ _ K => PEqualNP.QuantumGravity.Helpers.exists_stationary K
