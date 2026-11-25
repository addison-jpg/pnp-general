import PEqualNP.MetaComplexity.Helpers.EdgeUpper
import PEqualNP.Outside.L_meta_548

/-!
# A complete bipartite subgraph saves `(p - 1)(b - 1)` gates in the edge function

Let `T` be a vertex cover of `G`, and let `P ⊆ T` and `B` be disjoint nonempty sets with every
`p ∈ P` adjacent to every `b ∈ B` (a copy of `K_{|P|,|B|}`, not necessarily induced). Then the edge
function of `G` has a fan-in two circuit with `s` gates, where

    s + 1 + (|P| - 1)(|B| - 1) ≤ |E| + |T|.

The circuit computes `z = OR of x_b, b ∈ B` once (`|B| - 1` gates) and reads it at every `p ∈ P`:
the `|P| |B|` edges between `P` and `B` become `|P|` edges `p z` on one more input, the cover is
unchanged, and `plug` (L-meta-548) substitutes `z`. With `|P| = |B| = 2` this is the 4-cycle saving
of `EdgeFnC4.lean`; on a graph with a copy of `K_{p,p}` inside a cover it saves `(p - 1)^2` gates
below the value `|E| + tau - 1`.
-/

namespace PEqualNP.MetaComplexity.EdgeFn.Biclique

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.EdgeUpper

open Classical in
theorem biclique_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T P B : Finset (Fin n)) (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hPT : P ⊆ T) (hPB : Disjoint P B) (hP : P.Nonempty) (hB : B.Nonempty)
    (hadj : ∀ p ∈ P, ∀ b ∈ B, G.Adj p b) :
    ∃ s, HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s ∧
      s + 1 + (P.card - 1) * (B.card - 1) ≤ G.edgeFinset.card + T.card := by
  set ι : Fin n → Fin (n + 1) := Fin.castSucc
  set z : Fin (n + 1) := Fin.last n
  set Q : Finset (Sym2 (Fin n)) := (P ×ˢ B).image (fun q => s(q.1, q.2)) with hQ
  set E0 := G.edgeFinset \ Q with hE0
  set Ep : Finset (Sym2 (Fin (n + 1))) :=
    E0.image (Sym2.map ι) ∪ P.image (fun p => s(ι p, z)) with hEp
  set Tp : Finset (Fin (n + 1)) := T.image ι with hTp
  have hnPB : ∀ p ∈ P, p ∉ B := fun p hp hb => Finset.disjoint_left.1 hPB hp hb
  have hQsub : Q ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨⟨p, b⟩, hpb, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb
    simpa using hadj p hp b hb
  have hQcard : Q.card = P.card * B.card := by
    rw [hQ, Finset.card_image_of_injOn, Finset.card_product]
    rintro ⟨p, b⟩ hpb ⟨p', b'⟩ hpb' he
    obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb
    obtain ⟨hp', hb'⟩ := Finset.mem_product.1 hpb'
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hb (hnPB _ hp')
  have hE0card : E0.card + P.card * B.card = G.edgeFinset.card := by
    rw [hE0, Finset.card_sdiff_of_subset hQsub, hQcard]
    have := Finset.card_le_card hQsub
    omega
  have hEpcard : Ep.card + P.card * B.card ≤ G.edgeFinset.card + P.card := by
    have h1 := Finset.card_union_le (E0.image (Sym2.map ι)) (P.image (fun p => s(ι p, z)))
    have h2 := Finset.card_image_le (s := E0) (f := Sym2.map ι)
    have h3 := Finset.card_image_le (s := P) (f := fun p => s(ι p, z))
    rw [hEp]
    omega
  have hTpcard : Tp.card = T.card := Finset.card_image_of_injective _ (Fin.castSucc_injective n)
  have hEpne : Ep.Nonempty := by
    obtain ⟨p, hp⟩ := hP
    exact ⟨s(ι p, z), by rw [hEp]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  have hcov : ∀ e ∈ Ep, ∃ t ∈ Tp, t ∈ e := by
    intro e he
    rw [hEp, Finset.mem_union, Finset.mem_image, Finset.mem_image] at he
    rcases he with ⟨e0, he0, rfl⟩ | ⟨p, hp, rfl⟩
    · revert he0
      refine Sym2.ind (fun i j => ?_) e0
      intro he0
      have hij : G.Adj i j := by
        have := (Finset.mem_sdiff.1 he0).1
        simpa using this
      rcases hT i j hij with h | h
      · exact ⟨ι i, Finset.mem_image_of_mem _ h, by simp⟩
      · exact ⟨ι j, Finset.mem_image_of_mem _ h, by simp⟩
    · exact ⟨ι p, Finset.mem_image_of_mem _ (hPT hp), Sym2.mem_mk_left _ _⟩
  have hH := bld_hasCircuitSize (bld_edges (n + 1) Tp Ep hEpne hcov)
  -- `z = OR of x_b, b ∈ B`
  have hBc : HasCircuitSize n (fun x : Fin n → Bool => decide (∃ v ∈ B, x v = true))
      (B.card - 1) := bld_hasCircuitSize (bld_anyFinset B hB)
  have hlive : ∃ x : Fin n → Bool, decide (∃ v ∈ B, x v = true) = true := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨fun _ => true, decide_eq_true ⟨b, hb, rfl⟩⟩
  obtain ⟨C, hC, hsz, hev⟩ := Gap548Circuit.plug _ _ hBc hH hlive
  refine ⟨_, ⟨C, hC, le_rfl, fun x => ?_⟩, ?_⟩
  swap
  · rw [hTpcard] at hsz
    have hPc := hP.card_pos
    have hBc' := hB.card_pos
    have hmul : (P.card - 1) * (B.card - 1) + P.card + B.card = P.card * B.card + 1 := by
      obtain ⟨p, hp⟩ : ∃ p, P.card = p + 1 := ⟨P.card - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, B.card = b + 1 := ⟨B.card - 1, by omega⟩
      rw [hp, hb]
      simp only [Nat.add_sub_cancel]
      ring
    have := hEpcard
    -- `s = (|B| - 1) + (|Ep| + |T| - 1)`
    have hEp1 : 1 ≤ Ep.card := hEpne.card_pos
    omega
  rw [hev x]
  set y : Fin (n + 1) → Bool := Fin.snoc x (decide (∃ v ∈ B, x v = true)) with hy
  have yι : ∀ i, y (ι i) = x i := fun i => by simp [hy, ι]
  have yz : y z = decide (∃ v ∈ B, x v = true) := by simp [hy, z]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, hv⟩
    rw [hEp, Finset.mem_union, Finset.mem_image, Finset.mem_image] at he
    rcases he with ⟨e0, he0, rfl⟩ | ⟨p, hp, rfl⟩
    · revert he0 hv
      refine Sym2.ind (fun i j => ?_) e0
      intro he0 hv
      have hij : G.Adj i j := by
        have := (Finset.mem_sdiff.1 he0).1
        simpa using this
      refine ⟨i, j, hij, ?_, ?_⟩
      · rw [← yι]; exact hv _ (by simp)
      · rw [← yι]; exact hv _ (by simp)
    · have hpx : x p = true := by rw [← yι]; exact hv _ (Sym2.mem_mk_left _ _)
      have hzx : decide (∃ v ∈ B, x v = true) = true := by
        rw [← yz]; exact hv _ (Sym2.mem_mk_right _ _)
      obtain ⟨b, hb, hbx⟩ := of_decide_eq_true hzx
      exact ⟨p, b, hadj p hp b hb, hpx, hbx⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    by_cases hq : s(i, j) ∈ Q
    · obtain ⟨⟨p, b⟩, hpb, he⟩ := Finset.mem_image.1 hq
      obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb
      have hpb' : x p = true ∧ x b = true := by
        simp only [Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hi, hj⟩
        · exact ⟨hj, hi⟩
      refine ⟨s(ι p, z), by rw [hEp]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp),
        fun v hv => ?_⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact (yι _).trans hpb'.1
      · exact yz.trans (decide_eq_true ⟨b, hb, hpb'.2⟩)
    · refine ⟨Sym2.map ι s(i, j), ?_, fun v hv => ?_⟩
      · rw [hEp, Finset.mem_union]
        left
        exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨by simpa using hij, hq⟩)
      · simp only [Sym2.map_mk, Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact (yι _).trans hi
        · exact (yι _).trans hj

end PEqualNP.MetaComplexity.EdgeFn.Biclique
