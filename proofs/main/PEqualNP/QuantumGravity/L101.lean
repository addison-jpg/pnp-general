import PEqualNP.QuantumGravity.Gaps
import PEqualNP.QuantumGravity.Helpers.LocalGates

/-! L-qg-101: exponential complexity for local reversible circuits. If
`((n + 1)^3 * 8! + 1)^k < (2^n)!`, some reversible map of `n` bits has no circuit of at most `k`
gates that each act on at most three bits. The count of local gates is
`(localGates n).ncard ≤ (n + 1)^3 * 8!` (`Helpers/LocalGates.lean`); the rest is L-qg-001. Since
`log ((2^n)!)` is of order `n 2^n` and the count of local gates is polynomial in `n`, `k` can be
taken of order `n 2^n / log n`. -/

theorem PEqualNP.QuantumGravity.L101 : PEqualNP.QuantumGravity.Gap.L101 :=
  fun n k h => PEqualNP.QuantumGravity.Helpers.exists_not_mem_reachableIn_localGates n k h
