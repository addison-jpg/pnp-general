import PEqualNP.Outside.L_meta_275

/-!
# Weight-`k` OR circuits for set systems with pairwise intersections at most one

Row L-meta-275 is the instance `n = 7`, `m = 4`, `k = 2` of the lemma `main` proved in its file.
The variable form: if `m` sets `S i ⊆ [n]` pairwise meet in at most one point and each has more
than `k` points, then every circuit of fan-in-two AND and OR gates with wires `o i` that are true
at the unit vector of every point of `S i` (and of no other point) and compute the OR over `S i`
on every input with at most `k` true bits has at least `k * m` gates.
-/

namespace PEqualNP.MetaComplexity.LinearSets

open PEqualNP.CircuitLowerBounds

theorem linear_sets_lb (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hk : ∀ i : Fin m, k + 1 ≤ (S i).card)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h4 : ∀ (i : Fin m) (p : Fin n),
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i)
    (h5 : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) :
    k * m ≤ C.size := by
  have := PEqualNP.Outside.L_meta_275.main n m k S C o (fun _ => k) hS hgates h4 h5
    (fun _ => le_rfl) hk
  simpa [Finset.sum_const, mul_comm] using this

end PEqualNP.MetaComplexity.LinearSets
