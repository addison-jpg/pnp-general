import PEqualNP.S612.Statement
import PEqualNP.MetaComplexity.Helpers.EdgeFnWindow4

/-!
# L-meta-612 on the window classes

The target of L-meta-612 holds on two hereditary classes of C4-free graphs, by the checked
lower bounds for circuits WITH NOT gates (monotone circuits are a special case):

* `target_W6`: graphs in `W6` (every cycle has length at least 6 and six consecutive vertices of
  degree at most 2), any degree. Contains forests and girth >= 7 with hubs >= 7 apart.
* `target_W4`: graphs of maximum degree 3 in `W4` (every cycle has length at least 5 and four
  consecutive vertices of degree at most 2). Contains girth >= 5 with hubs >= 5 apart.
-/

namespace PEqualNP.Outside.S612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem hasCircuitSize_of_mono {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hev : ∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) :
    HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) C.size := by
  refine ⟨C, fun g hg => ⟨?_, (hC g hg).2⟩, le_rfl, fun x => ?_⟩
  · have h := (hC g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  · have := hev x
    by_cases h : ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true
    · simp [this.2 h, h]
    · have h' : C.eval (List.ofFn x) = false := by
        cases hc : C.eval (List.ofFn x)
        · rfl
        · exact absurd (this.1 hc) h
      simp [h', h]

theorem target_W6 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    PEqualNP.MetaComplexity.EdgeFn.Window.W6 G →
    (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hW hmin hC hev
  have := PEqualNP.MetaComplexity.EdgeFn.Window.w6_lb n t C.size G ∅ hW
    (fun i j _ => Finset.notMem_empty i) (fun T hT => hmin T hT) (hasCircuitSize_of_mono G C hC hev)
  simpa using this

theorem target_W4 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    (∃ u v : Fin n, G.Adj u v) →
    (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) →
    PEqualNP.MetaComplexity.EdgeFn.Window4.W4 G →
    (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hE hdeg hW hmin hC hev
  have := PEqualNP.MetaComplexity.EdgeFn.Window4.w4_lb n t C.size G ∅ hdeg hW
    (fun i j _ => Finset.notMem_empty i) (Or.inr hE) (fun T hT => hmin T hT)
    (hasCircuitSize_of_mono G C hC hev)
  simpa using this

end PEqualNP.Outside.S612
