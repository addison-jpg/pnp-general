import PEqualNP.General.XorExtension

/-!
# Iterating the XOR extension over `k` fresh variables

`extIter k f` is the function `x₁ ⊕ ... ⊕ x_k ⊕ f` on `n + k` inputs: each step adds one fresh
last input, as in `xor_lower` and `L_meta_716`.

* `iter_lower`: a circuit with `s + 3 k` gates for `extIter k f` gives circuits with `s` gates
  for `f` and for `¬f`, when `f` is non-constant. In words:
  `C(x₁ ⊕ ... ⊕ x_k ⊕ f) ≥ max (C f) (C ¬f) + 3 k`.
* `iter_upper`: if `f` or `¬f` has a circuit with `s` gates, then `extIter k f` has a circuit
  with `s + 4 k` gates. In words: `C(x₁ ⊕ ... ⊕ x_k ⊕ f) ≤ min (C f) (C ¬f) + 4 k`.

The lower bound does not use the exact value `min + 4` of one step. The two bounds differ by
`k - (max - min) ≥ k - 1`, so they agree only for `k = 1`.
-/

namespace PEqualNP.General.XorIterate

open PEqualNP.MetaComplexity

/-- One extension step: `x ⊕ f` with `x` the fresh last input. -/
def ext (n : ℕ) (f : (Fin n → Bool) → Bool) : (Fin (n + 1) → Bool) → Bool :=
  fun x => xor (x (Fin.last n)) (f (fun i : Fin n => x i.castSucc))

/-- `k` fresh variables, added one at a time. -/
def extIter (n : ℕ) (f : (Fin n → Bool) → Bool) : (k : ℕ) → (Fin (n + k) → Bool) → Bool
  | 0 => f
  | k + 1 => ext (n + k) (extIter n f k)

lemma ext_nonconst (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    ∃ y y' : Fin (n + 1) → Bool, ext n f y ≠ ext n f y' := by
  obtain ⟨y, y', hne⟩ := hf
  refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
  simpa [ext] using hne

lemma extIter_nonconst (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    ∀ k : ℕ, ∃ y y' : Fin (n + k) → Bool, extIter n f k y ≠ extIter n f k y'
  | 0 => hf
  | k + 1 => ext_nonconst (n + k) _ (extIter_nonconst n f hf k)

/-- Lower bound for `k + 1` fresh variables:
`C(x₁ ⊕ ... ⊕ x_{k+1} ⊕ f) ≥ max (C f) (C ¬f) + 3 (k + 1)`. -/
theorem iter_lower (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    ∀ (k s : ℕ), HasCircuitSize (n + (k + 1)) (extIter n f (k + 1)) (s + 3 * (k + 1)) →
      HasCircuitSize n f s ∧ HasCircuitSize n (fun y : Fin n → Bool => !f y) s
  | 0, s, h => PEqualNP.General.XorExtension.xor_lower n s f hf h
  | k + 1, s, h => by
      have h' : HasCircuitSize (n + (k + 1) + 1) (ext (n + (k + 1)) (extIter n f (k + 1)))
          ((s + 3 * (k + 1)) + 3) := by
        have : s + 3 * (k + 1 + 1) = (s + 3 * (k + 1)) + 3 := by omega
        rw [← this]; exact h
      exact iter_lower n f hf k s
        (PEqualNP.General.XorExtension.xor_lower (n + (k + 1)) (s + 3 * (k + 1))
          (extIter n f (k + 1)) (extIter_nonconst n f hf (k + 1)) h').1

/-- Upper bound for `k` fresh variables: `C(x₁ ⊕ ... ⊕ x_k ⊕ f) ≤ min (C f) (C ¬f) + 4 k`. -/
theorem iter_upper (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s ∨ HasCircuitSize n (fun y : Fin n → Bool => !f y) s) :
    ∀ k : ℕ, HasCircuitSize (n + (k + 1)) (extIter n f (k + 1)) (s + 4 * (k + 1))
  | 0 => by
      rcases h with h | h
      · exact (PEqualNP.Outside.L_meta_716 n s f).1 h
      · exact (PEqualNP.Outside.L_meta_716 n s f).2 h
  | k + 1 => by
      have := (PEqualNP.Outside.L_meta_716 (n + (k + 1)) (s + 4 * (k + 1))
        (extIter n f (k + 1))).1 (iter_upper n f s h k)
      have e : s + 4 * (k + 1 + 1) = (s + 4 * (k + 1)) + 4 := by omega
      rw [e]; exact this

#print axioms iter_lower
#print axioms iter_upper

end PEqualNP.General.XorIterate
