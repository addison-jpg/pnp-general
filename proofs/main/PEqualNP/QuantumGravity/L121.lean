import PEqualNP.QuantumGravity.L102
import PEqualNP.QuantumGravity.L127

/-! L-qg-121: Deutsch's quantum consistency for the classical case embedded. Every quantum channel on
`Fin d`, `d > 0`, that maps matrices diagonal in the computational basis to diagonal matrices has a
fixed density matrix that is diagonal. Row L-qg-127 derives it from L-qg-102 (every Markov kernel on
a nonempty finite register has a stationary distribution), which is checked. -/

theorem PEqualNP.QuantumGravity.L121 : PEqualNP.QuantumGravity.Gap.L121 :=
  PEqualNP.QuantumGravity.L127 PEqualNP.QuantumGravity.L102
