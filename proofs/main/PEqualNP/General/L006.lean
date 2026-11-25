import PEqualNP.General.XorExtension

/-! L-gen-006: the exact cost of XOR with a fresh input when the sizes of `f` and `¬f` differ.
If some size `s₀` is enough for exactly one of `f`, `¬f` (so `C f ≠ C ¬f`), then `x ⊕ f` has a
circuit with `t + 4` gates exactly when `f` or `¬f` has one with `t` gates:
`C(x ⊕ f) = min (C f) (C ¬f) + 4`. Lower bound: L-gen-005. Upper bound: L-meta-716.
The case `C f = C ¬f` is open (`research/notes/general/generalize-xor-extension.md`). -/

theorem PEqualNP.General.L006 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      (∃ y y' : Fin n → Bool, f y ≠ f y') →
      ∀ s₀ : ℕ,
        ((PEqualNP.MetaComplexity.HasCircuitSize n f s₀ ∧
            ¬ PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !f y) s₀) ∨
          (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !f y) s₀ ∧
            ¬ PEqualNP.MetaComplexity.HasCircuitSize n f s₀)) →
        ∀ t : ℕ,
          (PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
              (fun x : Fin (n + 1) → Bool =>
                xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc))) (t + 4) ↔
            (PEqualNP.MetaComplexity.HasCircuitSize n f t ∨
              PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !f y) t)) :=
  PEqualNP.General.XorExtension.xor_exact
