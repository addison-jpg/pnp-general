import PEqualNP.QuantumGravity.Gaps
import PEqualNP.QuantumGravity.Helpers.ChannelFixedPoint

/-! L-qg-120: Deutsch's consistency condition for a quantum register. Every quantum channel on
`Fin d`, `d > 0`, given in Kraus form, has a fixed density matrix. The density matrices form a
nonempty, compact, convex subset of the real vector space of complex `d × d` matrices (every entry
has norm at most 2), the channel is real-linear and maps that set into itself (L-qg-122), and the
fixed-point lemma of `Helpers/FixedPoint.lean` (Cesàro averages, the lemma behind L-qg-102) applies.
With L-qg-126 this gives L-qg-121 a second time. -/

theorem PEqualNP.QuantumGravity.L120 : PEqualNP.QuantumGravity.Gap.L120 :=
  fun _ _ _ _ hd hK => PEqualNP.QuantumGravity.Helpers.exists_fixed_densityMatrix hd hK
