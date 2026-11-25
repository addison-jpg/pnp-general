import PEqualNP.MetaComplexity.Helpers.EdgeFnWindow
import PEqualNP.MetaComplexity.L658
import PEqualNP.Outside.L_meta_568

/-!
# The edge-function lower bound on the window-of-four class

Row L-meta-658 proves the bound `|A| + |E| + k ≤ s + 1` on graphs of maximum degree 3 with no
cycle of length 3 or 4 in which every vertex-deleted subgraph with an edge has a good leaf or a
run of four, GIVEN the statement of row L-meta-568 (the free-input chain law). That row is proved
in `Outside/L_meta_568.lean`, so the bound holds outright (`l658_full`).

The class `W4`: every cycle has length at least 5 and has four cyclically consecutive vertices
with at most two neighbours each. With maximum degree 3 it meets the hypotheses of L-meta-658
(`w4_dich`: a vertex-deleted subgraph is a forest, with a good leaf, or has a cycle, whose window
of four is a run of four). `w4_lb` is the bound on maximum degree 3 graphs of `W4`.

`W4` contains `W6`. With maximum degree 3 it adds, for example, the 5-cycle and the 6-cycle with a
pendant leaf, the smallest graphs on which the proof of L-meta-204 does not apply (Note 1).
-/

namespace PEqualNP.MetaComplexity.EdgeFn.Window4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.EdgeFn.Window
open SimpleGraph

/-- The window-of-four class: every cycle has length at least 5 and four cyclically consecutive
vertices (positions `i + 1 .. i + 4`) with at most two neighbours each. -/
def W4 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 5 ≤ c.length ∧
    ∃ i : ℕ, ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
      (G.neighborSet (c.getVert ((i + j) % c.length))).ncard ≤ 2

/-- A window of four on a cycle of length at least 5 is a run of four. -/
theorem r4_of_window {n : ℕ} {H : SimpleGraph (Fin n)} {v : Fin n} (c : H.Walk v v)
    (hc : c.IsCycle) (h5 : 5 ≤ c.length) (i : ℕ)
    (hi : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → (H.neighborSet (c.getVert ((i + j) % c.length))).ncard ≤ 2) :
    ∃ q0 q1 q2 q3 q4 q5 : Fin n, [q1, q2, q3, q4].Nodup ∧ q0 ∉ [q1, q2, q3, q4] ∧
      q5 ∉ [q1, q2, q3, q4] ∧ (∀ w : Fin n, H.Adj q1 w ↔ w = q0 ∨ w = q2) ∧
      (∀ w : Fin n, H.Adj q2 w ↔ w = q1 ∨ w = q3) ∧ (∀ w : Fin n, H.Adj q3 w ↔ w = q2 ∨ w = q4) ∧
      (∀ w : Fin n, H.Adj q4 w ↔ w = q3 ∨ w = q5) := by
  set L := c.length with hL
  have hL0 : 0 < L := by omega
  let f : ℕ → Fin n := fun j => c.getVert ((i + j) % L)
  have adj : ∀ j, H.Adj (f j) (f (j + 1)) := fun j => cyc_adj c hL0 i j
  have ne : ∀ j j', j ≤ 5 → j' ≤ 5 → j ≠ j' → (j = 0 → j' ≠ 5) → (j = 5 → j' ≠ 0) →
      f j ≠ f j' := by
    intro j j' hj hj' hjj' h05 h50
    have hmod : (i + j) % L ≠ (i + j') % L := by
      rcases Nat.lt_or_gt_of_ne hjj' with hlt | hlt
      · refine mod_ne L i j j' hlt ?_
        by_cases h0 : j = 0
        · have := h05 h0; omega
        · omega
      · refine fun h => mod_ne L i j' j hlt ?_ h.symm
        by_cases h0 : j' = 0
        · have : j ≠ 5 := fun e => h50 e h0; omega
        · omega
    have := cyc_ne hc (i := i + j) (j := i + j') (by simpa [Nat.mod_mod] using hmod)
    simpa [Nat.mod_mod] using this
  have inner : ∀ j, 1 ≤ j → j ≤ 4 → ∀ w, H.Adj (f j) w ↔ w = f (j - 1) ∨ w = f (j + 1) := by
    intro j h1 h4 w
    have hprev : H.Adj (f j) (f (j - 1)) := by
      have := adj (j - 1)
      rw [show j - 1 + 1 = j by omega] at this
      exact this.symm
    constructor
    · exact nb_two (hi j h1 h4) hprev (adj j)
        (ne (j - 1) (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)) w
    · rintro (rfl | rfl)
      · exact hprev
      · exact adj j
  have nn : ∀ j j', j ≤ 5 → 1 ≤ j' → j' ≤ 4 → j ≠ j' → f j ≠ f j' := fun j j' hj h1 h4 hne =>
    ne j j' hj (by omega) hne (by omega) (by omega)
  refine ⟨f 0, f 1, f 2, f 3, f 4, f 5, ?_, ?_, ?_, inner 1 le_rfl (by norm_num),
    inner 2 (by norm_num) (by norm_num), inner 3 (by norm_num) (by norm_num),
    inner 4 (by norm_num) le_rfl⟩
  · have hinj : Function.Injective (fun k : Fin 4 => f (k + 1)) := fun k k' h => by
      by_contra hk
      exact nn (k + 1) (k' + 1) (by omega) (by omega) (by omega)
        (fun e => hk (Fin.ext (by simpa using e))) h
    have := List.nodup_ofFn.2 hinj
    simpa [List.ofFn_succ] using this
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact nn 0 1 (by norm_num) le_rfl (by norm_num) (by norm_num) h
    · exact nn 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    · exact nn 0 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    · exact nn 0 4 (by norm_num) (by norm_num) le_rfl (by norm_num) h
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact nn 5 1 le_rfl le_rfl (by norm_num) (by norm_num) h
    · exact nn 5 2 le_rfl (by norm_num) (by norm_num) (by norm_num) h
    · exact nn 5 3 le_rfl (by norm_num) (by norm_num) (by norm_num) h
    · exact nn 5 4 le_rfl (by norm_num) le_rfl (by norm_num) h

/-- `W4` passes to vertex-deleted subgraphs (`Peel.delVerts`). -/
theorem w4_delVerts {n : ℕ} (G : SimpleGraph (Fin n)) (hW : W4 G) (X : Finset (Fin n)) :
    W4 (PEqualNP.Library.Peel.delVerts G X) := by
  intro v c hc
  have hle : PEqualNP.Library.Peel.delVerts G X ≤ G := fun i j h => h.1
  obtain ⟨h5, i, hi⟩ := hW v (c.mapLe hle) (hc.mapLe hle)
  rw [Walk.length_mapLe] at h5 hi
  refine ⟨h5, i, fun j h1 h4 => ?_⟩
  have := hi j h1 h4
  rw [Walk.mapLe, Walk.getVert_map] at this
  have hsub : ∀ w, (PEqualNP.Library.Peel.delVerts G X).neighborSet w ⊆ G.neighborSet w :=
    fun w y hy => hle hy
  exact le_trans (Set.ncard_le_ncard (hsub _) (Set.toFinite _)) this

/-- The dichotomy L-meta-658 asks for, on `W4`. -/
theorem w4_dich {n : ℕ} (G : SimpleGraph (Fin n)) (hW : W4 G) (X : Finset (Fin n))
    (hE : ∃ i j : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj i j) :
    PEqualNP.Library.Peel.GoodLeaf (PEqualNP.Library.Peel.delVerts G X) ∨
      ∃ q0 q1 q2 q3 q4 q5 : Fin n, [q1, q2, q3, q4].Nodup ∧ q0 ∉ [q1, q2, q3, q4] ∧
        q5 ∉ [q1, q2, q3, q4] ∧
        (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q1 w ↔ w = q0 ∨ w = q2) ∧
        (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q2 w ↔ w = q1 ∨ w = q3) ∧
        (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q3 w ↔ w = q2 ∨ w = q4) ∧
        (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q4 w ↔ w = q3 ∨ w = q5) := by
  set H := PEqualNP.Library.Peel.delVerts G X
  by_cases hac : H.IsAcyclic
  · exact Or.inl (Forest.forest_good_leaf H hac hE)
  · rw [IsAcyclic] at hac
    push Not at hac
    obtain ⟨v, c, hc⟩ := hac
    obtain ⟨h5, i, hi⟩ := w4_delVerts G hW X v c hc
    exact Or.inr (r4_of_window c hc h5 i hi)

/-- The lower bound on the window-of-four class with maximum degree 3: for `G` of maximum degree
3 in `W4`, `A` a set of inputs that no edge meets, and `k` at most every vertex cover, every
fan-in two circuit over AND, OR, NOT (every gate counted) for "some input of `A` is true, or both
ends of some edge are true" has at least `|A| + |E| + k - 1` gates. -/
theorem w4_lb : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) → W4 G →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s →
    A.card + G.edgeSet.ncard + k ≤ s + 1 := by
  intro n k s G A hdeg hW hinv hne hk hC
  exact PEqualNP.MetaComplexity.L658 PEqualNP.Outside.L_meta_568 n k s G A hdeg (fun v c hc => (hW v c hc).1) (w4_dich G hW) hinv hne hk hC

/-- `W6` is inside `W4`. -/
theorem w6_w4 {n : ℕ} (G : SimpleGraph (Fin n)) (hW : W6 G) : W4 G := by
  intro v c hc
  obtain ⟨h6, i, hi⟩ := hW v c hc
  exact ⟨by omega, i, fun j _ h4 => hi j (by omega)⟩

/-- The exact size on maximum degree 3 graphs of `W4`: with an edge and `T` a least vertex cover,
the edge function has a fan-in two circuit with `s` gates exactly when `|E| + |T| ≤ s + 1`. -/
theorem w4_exact (n s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) (hW : W4 G)
    (hE : ∃ i j : Fin n, G.Adj i j) (T : Finset (Fin n))
    (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hmin : ∀ T' : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s ↔
    G.edgeFinset.card + T.card ≤ s + 1 := by
  constructor
  · intro hC
    have hC' : HasCircuitSize n
        (fun x : Fin n → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s := by
      obtain ⟨C, hC, hs, hev⟩ := hC
      refine ⟨C, hC, hs, fun x => ?_⟩
      rw [hev x]
      simp
    have := w4_lb n T.card s G ∅ hdeg hW (fun i j _ => Finset.notMem_empty i) (Or.inr hE) hmin hC'
    have hec : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    rw [hec, Finset.card_empty] at this
    omega
  · intro hs
    obtain ⟨D, hD, -, hDfun, hDsize⟩ := Helpers.NotFreeCor.nfc_edge_upper_mono n G T hE hT
    exact ⟨D, hD, by omega, fun x => congrFun hDfun x⟩

/-- NOT gates never save a gate on maximum degree 3 graphs of `W4`: every fan-in two circuit for the
edge function has an equivalent one with no NOT gate and no more gates (the NOT gate ladder
collapses to rung 0 on this class). -/
theorem w4_not_free (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) (hW : W4 G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : FanInTwo C)
    (hfun : circuitFun n C =
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, FanInTwo D ∧
      (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      circuitFun n D = circuitFun n C ∧ D.size ≤ C.size := by
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · obtain ⟨T, hT, hTc⟩ := Loc.tau_attained G
    have hmin : ∀ T' : Finset (Fin n),
        (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := fun T' hT' =>
      hTc ▸ Loc.tau_le G T' hT'
    have hlb := (w4_exact n C.size G hdeg hW hE T hT hmin).1 ⟨C, hC, le_rfl, fun x => congrFun hfun x⟩
    obtain ⟨D, hD, hDnot, hDfun, hDsize⟩ := Helpers.NotFreeCor.nfc_edge_upper_mono n G T hE hT
    exact ⟨D, hD, hDnot, hDfun.trans hfun.symm, by omega⟩
  · exact Window.w6_not_free n G (fun v c hc => absurd hc (by
      intro hcyc
      obtain ⟨i, j, hij⟩ : ∃ i j, G.Adj i j := by
        cases c with
        | nil => exact absurd hcyc (by simp)
        | cons h _ => exact ⟨_, _, h⟩
      exact hE ⟨i, j, hij⟩)) C hC hfun

end PEqualNP.MetaComplexity.EdgeFn.Window4
