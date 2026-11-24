import PEqualNP.General.NegLiteral

/-! L-gen-007: the cost of a negated fresh input. Circuits of AND, OR and NOT gates of fan-in at
most two, any number of NOT gates, every gate counted (`HasCircuitSize`). For a non-constant `f`
and a fresh input `x`: a circuit with `s + 1` gates for `¬x ∧ f` gives one with `s` gates for
`f`, and a circuit with `s` gates for `f` gives one with `s + 2` gates for `¬x ∧ f`. In words:
`C f + 1 ≤ C(¬x ∧ f) ≤ C f + 2`. (For the positive input, `C(x ∧ f) = C f + 1` exactly:
L-meta-174.) Proof: `PEqualNP.General.XorExtension.restrict_one`, gate elimination on either
side. -/

theorem PEqualNP.General.L007 :
    ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
      (∃ y y' : Fin n → Bool, f y ≠ f y') →
      (PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
          (fun x : Fin (n + 1) → Bool => !x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
          (s + 1) → PEqualNP.MetaComplexity.HasCircuitSize n f s) ∧
        (PEqualNP.MetaComplexity.HasCircuitSize n f s →
          PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
            (fun x : Fin (n + 1) → Bool => !x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
            (s + 2)) :=
  fun n s f hf => ⟨PEqualNP.General.XorExtension.neg_and_lower n s f hf,
    PEqualNP.General.XorExtension.neg_and_upper n s f⟩
