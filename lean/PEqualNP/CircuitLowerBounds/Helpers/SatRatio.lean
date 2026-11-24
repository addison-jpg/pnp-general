import PEqualNP.CircuitLowerBounds.L041

/-!
# SAT has no circuits of size `(a / b) n + c` for any `a / b < 5 / 4`

Row L-clb-040 states the bound for the ratio `99 / 100`. Row L-clb-041 (SAT at length `4 k + 2`
needs `5 k + 1` gates, `k ≥ 4`) gives every ratio below `5 / 4`: for all `a, b` with `4 a < 5 b`
and every `c`, no size bound `s` with `b * s n ≤ a * n + c` for all `n` puts SAT in `SIZE s`.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.SatRatio

theorem sat_ratio (a b : ℕ) (hab : 4 * a < 5 * b) :
    ¬ ∃ (s : ℕ → ℕ) (c : ℕ), (∀ n : ℕ, b * s n ≤ a * n + c) ∧
      PEqualNP.Search.SAT ∈ PEqualNP.CircuitLowerBounds.SIZE s := by
  rintro ⟨s, c, hs, hS⟩
  set k := 2 * a + c + 4 with hk
  obtain ⟨D, hD, hsz, hdec⟩ := hS (4 * k + 2)
  have h5 := PEqualNP.CircuitLowerBounds.L041 k (by omega) D hD hdec
  have h1 := hs (4 * k + 2)
  have h2 : b * (5 * k + 1) ≤ b * s (4 * k + 2) :=
    Nat.mul_le_mul_left b (le_trans h5 hsz)
  -- `b (5 k + 1) ≥ (4 a + 1) k + b > a (4 k + 2) + c`
  have h3 : (4 * a + 1) * k ≤ 5 * b * k := Nat.mul_le_mul_right k (by omega)
  nlinarith

end PEqualNP.CircuitLowerBounds.Helpers.SatRatio
