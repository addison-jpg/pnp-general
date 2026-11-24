import PEqualNP.QuantumGravity.Helpers.GateWords

/-! L-qg-006: linear complexity growth up to an exponential length, along one gate word. For a
finite gate set `S` that generates every reversible map of `n` bits, if `(|S| + 1)^k < (2^n)!`
then there is a word of more than `k` gates from `S` whose first `t` gates have complexity exactly
`t`, for every `t` up to its length. Brown and Susskind conjecture this growth for random
circuits and for time-independent Hamiltonians; this row is the classical statement for one
chosen word. -/

theorem PEqualNP.QuantumGravity.L006 :
    ∀ (n : ℕ) (S : Finset (Equiv.Perm (Fin n → Bool))) (k : ℕ),
      (∀ g, ∃ m,
        g ∈ PEqualNP.QuantumGravity.ReachableIn (S : Set (Equiv.Perm (Fin n → Bool))) m) →
      (S.card + 1) ^ k < (2 ^ n).factorial →
        ∃ l : List (Equiv.Perm (Fin n → Bool)), (∀ x ∈ l, x ∈ S) ∧ k < l.length ∧
          ∀ t ≤ l.length,
            (l.take t).prod ∈
                PEqualNP.QuantumGravity.ReachableIn (S : Set (Equiv.Perm (Fin n → Bool))) t ∧
              ∀ m < t, (l.take t).prod ∉
                PEqualNP.QuantumGravity.ReachableIn (S : Set (Equiv.Perm (Fin n → Bool))) m :=
  fun n S k hgen h => PEqualNP.QuantumGravity.Helpers.exists_long_minimal_word n S k hgen h
