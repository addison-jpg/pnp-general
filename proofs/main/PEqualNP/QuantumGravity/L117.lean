import PEqualNP.QuantumGravity.Helpers.Circuits

/-! L-qg-117: the bound on the Haar measure of a ball (gap L-qg-115) implies the quantum counting
bound in Knill's form (gap L-qg-116), with the same constant. The unitaries within `ε` of a
product of at most `k` gates from `S` lie in at most `(|S| + 1)^k` operator norm balls of radius
`ε` (L-qg-001), and the measure of a union is at most the sum of the measures. -/

theorem PEqualNP.QuantumGravity.L117 : PEqualNP.QuantumGravity.Gap.L117 :=
  PEqualNP.QuantumGravity.Helpers.knill_of_ball
