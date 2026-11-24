import PEqualNP.General.XorExtension

/-! L-gen-005: XOR with a fresh input costs at least three gates more than both `f` and `¬f`.
Circuits of AND, OR and NOT gates of fan-in at most two, any number of NOT gates, every gate
counted (`HasCircuitSize`). For a non-constant `f`, a circuit with `s + 3` gates for `x ⊕ f`
gives circuits with `s` gates for `f` and for `¬f`. In words:
`C(x ⊕ f) ≥ max (C f) (C ¬f) + 3`. The proof is gate elimination with no minimality assumption
(`PEqualNP.General.XorExtension`). -/

theorem PEqualNP.General.L005 :
    ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
      (∃ y y' : Fin n → Bool, f y ≠ f y') →
      PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc)))
        (s + 3) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !f y) s :=
  PEqualNP.General.XorExtension.xor_lower
