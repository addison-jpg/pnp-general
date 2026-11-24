import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-002: for every finite gate set `S` of reversible maps of `n` bits, if
`(|S| + 1)^k < (2^n)!` then some reversible map of `n` bits has no circuit of at most `k` gates
from `S`. With `|S|` polynomial in `n`, `k` can be taken of order `n 2^n / log n`. -/

theorem PEqualNP.QuantumGravity.L002 :
    ∀ (n : ℕ) (S : Finset (Equiv.Perm (Fin n → Bool))) (k : ℕ),
      (S.card + 1) ^ k < (2 ^ n).factorial →
        ∃ g : Equiv.Perm (Fin n → Bool),
          g ∉ PEqualNP.QuantumGravity.ReachableIn (S : Set (Equiv.Perm (Fin n → Bool))) k := by
  intro n S k h
  exact PEqualNP.QuantumGravity.Helpers.exists_not_mem_reachableIn S k
    (by rw [PEqualNP.QuantumGravity.Helpers.nat_card_perm_bits]; exact h)
