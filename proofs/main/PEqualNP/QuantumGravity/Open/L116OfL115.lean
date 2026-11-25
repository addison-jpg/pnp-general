import PEqualNP.QuantumGravity.Helpers.Circuits

/-! Seat C1 of `open-qg`: the quantum counting bound (L-qg-116) follows from the Haar ball bound
(L-qg-115), with the same constant. The union bound is already proved in
`Helpers.knill_of_ball` (row L-qg-117: `ApproxReachableIn S k ε` lies in at most `(|S| + 1)^k`
operator norm balls, and the measure of a finite union is at most the sum). This file states it
under the seat's name. It does not prove L-qg-115 or L-qg-116 on their own. -/

theorem PEqualNP.QuantumGravity.Open.L116_of_L115 :
    PEqualNP.QuantumGravity.Gap.L115 → PEqualNP.QuantumGravity.Gap.L116 :=
  PEqualNP.QuantumGravity.Helpers.knill_of_ball
