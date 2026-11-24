import PEqualNP.QuantumGravity.Helpers.Ctc

/-! L-qg-010: a deterministic system with finitely many states that ever enters a set `H` of
states enters it within as many steps as it has states. Read with the holographic bound (a region
of boundary area `A` has at most `exp (A / 4)` states in Planck units), a computation confined to
the region halts within that many steps or never halts. The bound itself is a physics premise,
not part of this row. -/

theorem PEqualNP.QuantumGravity.L010 :
    ∀ (S : Type) [Fintype S] (f : S → S) (H : Set S) (x : S),
      (∃ t : ℕ, f^[t] x ∈ H) → ∃ t < Fintype.card S, f^[t] x ∈ H :=
  fun _ _ f H x hex => PEqualNP.QuantumGravity.Helpers.enters_within_card f H x hex
