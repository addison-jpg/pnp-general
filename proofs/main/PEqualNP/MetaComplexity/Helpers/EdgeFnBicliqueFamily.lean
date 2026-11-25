import PEqualNP.MetaComplexity.Helpers.EdgeUpper
import PEqualNP.Outside.L_meta_548

/-!
# A family of edge-disjoint bicliques saves `∑ (|P_i| - 1)(|B_i| - 1)` gates

Iterating `EdgeFnBiclique.biclique_upper`: if `T` covers `G` and `(P_i, B_i)` are bicliques with
`P_i ⊆ T`, `P_i`, `B_i` disjoint and nonempty, all `P_i × B_i` edges present, and the edge sets
`P_i × B_i` pairwise disjoint, the edge function has a circuit with `s` gates where
`s + 1 + ∑ (|P_i| - 1)(|B_i| - 1) ≤ |E| + |T|`.
-/

namespace PEqualNP.MetaComplexity.EdgeFn.BicliqueFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.EdgeUpper

/-- The edges between `P` and `B`. -/
def qset {n : ℕ} (P B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (P ×ˢ B).image (fun q => s(q.1, q.2))

theorem mem_qset {n : ℕ} {P B : Finset (Fin n)} {p b : Fin n} (hp : p ∈ P) (hb : b ∈ B) :
    s(p, b) ∈ qset P B :=
  Finset.mem_image.2 ⟨(p, b), Finset.mem_product.2 ⟨hp, hb⟩, rfl⟩

theorem qset_map {n : ℕ} (P B : Finset (Fin n)) :
    qset (P.image Fin.castSucc) (B.image Fin.castSucc) =
      (qset P B).image (Sym2.map (Fin.castSucc : Fin n → Fin (n + 1))) := by
  ext e
  simp only [qset, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, rfl⟩
    exact ⟨s(p, q), ⟨p, q, ⟨hp, hq⟩, rfl⟩, by simp⟩
  · rintro ⟨e0, ⟨p, q, ⟨hp, hq⟩, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, by simp⟩

theorem qset_card {n : ℕ} {P B : Finset (Fin n)} (hPB : Disjoint P B) :
    (qset P B).card = P.card * B.card := by
  rw [qset, Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨p, b⟩ hpb ⟨p', b'⟩ hpb' he
  obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb
  obtain ⟨hp', hb'⟩ := Finset.mem_product.1 hpb'
  simp only [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hb (Finset.disjoint_left.1 hPB hp')

open Classical in
theorem family_edges : ∀ (k n : ℕ) (L : List (Finset (Fin n) × Finset (Fin n))),
    L.length = k → ∀ (T : Finset (Fin n)) (E : Finset (Sym2 (Fin n))), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    (∀ pb ∈ L, pb.1 ⊆ T) → (∀ pb ∈ L, Disjoint pb.1 pb.2) →
    (∀ pb ∈ L, pb.1.Nonempty) → (∀ pb ∈ L, pb.2.Nonempty) →
    (∀ pb ∈ L, qset pb.1 pb.2 ⊆ E) →
    L.Pairwise (fun a b => Disjoint (qset a.1 a.2) (qset b.1 b.2)) →
    ∃ s, HasCircuitSize n (fun x : Fin n → Bool => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) s ∧
      s + 1 + (L.map (fun pb => (pb.1.card - 1) * (pb.2.card - 1))).sum ≤ E.card + T.card := by
  intro k
  induction k with
  | zero =>
    intro n L hL T E hE hcov _ _ _ _ _ _
    obtain rfl : L = [] := List.length_eq_zero_iff.1 hL
    refine ⟨_, bld_hasCircuitSize (bld_edges n T E hE hcov), ?_⟩
    have := hE.card_pos
    simp only [List.map_nil, List.sum_nil]
    omega
  | succ k ih =>
    intro n L hL T E hE hcov hPT hdis hPn hBn hQE hpw
    obtain ⟨⟨P, B⟩, L, rfl⟩ : ∃ hd L', L = hd :: L' := by
      cases L with
      | nil => simp at hL
      | cons a l => exact ⟨a, l, rfl⟩
    have hLk : L.length = k := by simpa using hL
    have hPT0 : P ⊆ T := hPT (P, B) (by simp)
    have hPB : Disjoint P B := hdis (P, B) (by simp)
    have hP : P.Nonempty := hPn (P, B) (by simp)
    have hB : B.Nonempty := hBn (P, B) (by simp)
    have hQ0 : qset P B ⊆ E := hQE (P, B) (by simp)
    rw [List.pairwise_cons] at hpw
    obtain ⟨hpw0, hpw1⟩ := hpw
    set ι : Fin n → Fin (n + 1) := Fin.castSucc with hι
    set z : Fin (n + 1) := Fin.last n with hz
    set Q := qset P B with hQ
    set E0 := E \ Q with hE0
    set Ep : Finset (Sym2 (Fin (n + 1))) :=
      E0.image (Sym2.map ι) ∪ P.image (fun p => s(ι p, z)) with hEp
    set Tp : Finset (Fin (n + 1)) := T.image ι with hTp
    have hQcard : Q.card = P.card * B.card := qset_card hPB
    have hE0card : E0.card + P.card * B.card = E.card := by
      rw [hE0, Finset.card_sdiff_of_subset hQ0, hQcard]
      have := Finset.card_le_card hQ0
      omega
    have hEpcard : Ep.card + P.card * B.card ≤ E.card + P.card := by
      have h1 := Finset.card_union_le (E0.image (Sym2.map ι)) (P.image (fun p => s(ι p, z)))
      have h2 := Finset.card_image_le (s := E0) (f := Sym2.map ι)
      have h3 := Finset.card_image_le (s := P) (f := fun p => s(ι p, z))
      rw [hEp]
      omega
    have hTpcard : Tp.card = T.card := Finset.card_image_of_injective _ (Fin.castSucc_injective n)
    have hEpne : Ep.Nonempty := by
      obtain ⟨p, hp⟩ := hP
      exact ⟨s(ι p, z), by rw [hEp]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
    have hcov' : ∀ e ∈ Ep, ∃ t ∈ Tp, t ∈ e := by
      intro e he
      rw [hEp, Finset.mem_union, Finset.mem_image, Finset.mem_image] at he
      rcases he with ⟨e0, he0, rfl⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨t, ht, hte⟩ := hcov e0 (Finset.mem_sdiff.1 he0).1
        exact ⟨ι t, Finset.mem_image_of_mem _ ht, by
          revert hte; refine Sym2.ind (fun i j => ?_) e0; intro h
          rcases Sym2.mem_iff.1 h with rfl | rfl <;> simp⟩
      · exact ⟨ι p, Finset.mem_image_of_mem _ (hPT0 hp), Sym2.mem_mk_left _ _⟩
    -- the tail family on `Fin (n+1)`
    set L' : List (Finset (Fin (n + 1)) × Finset (Fin (n + 1))) :=
      L.map (fun pb => (pb.1.image ι, pb.2.image ι)) with hL'
    have hmemL' : ∀ qr ∈ L', ∃ pb ∈ L, qr = (pb.1.image ι, pb.2.image ι) := by
      intro qr hq
      obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 hq
      exact ⟨pb, hpb, rfl⟩
    have hL'len : L'.length = k := by rw [hL', List.length_map, hLk]
    have hinj : Function.Injective ι := Fin.castSucc_injective n
    have hDis := ih (n + 1) L' hL'len Tp Ep hEpne hcov'
      (by
        intro qr hq
        obtain ⟨pb, hpb, rfl⟩ := hmemL' qr hq
        exact Finset.image_subset_image (hPT pb (List.mem_cons_of_mem _ hpb)))
      (by
        intro qr hq
        obtain ⟨pb, hpb, rfl⟩ := hmemL' qr hq
        exact (Finset.disjoint_image hinj).2 (hdis pb (List.mem_cons_of_mem _ hpb)))
      (by
        intro qr hq
        obtain ⟨pb, hpb, rfl⟩ := hmemL' qr hq
        exact (hPn pb (List.mem_cons_of_mem _ hpb)).image _)
      (by
        intro qr hq
        obtain ⟨pb, hpb, rfl⟩ := hmemL' qr hq
        exact (hBn pb (List.mem_cons_of_mem _ hpb)).image _)
      (by
        intro qr hq
        obtain ⟨pb, hpb, rfl⟩ := hmemL' qr hq
        show qset (pb.1.image ι) (pb.2.image ι) ⊆ Ep
        rw [hι, qset_map]
        intro e he
        obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
        rw [hEp, Finset.mem_union]
        left
        refine Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨hQE pb (List.mem_cons_of_mem _ hpb) he0, ?_⟩)
        intro h'
        exact Finset.disjoint_left.1 (hpw0 pb hpb) h' he0)
      (by
        rw [hL', List.pairwise_map]
        refine hpw1.imp ?_
        intro a b hab
        show Disjoint (qset (a.1.image ι) (a.2.image ι)) (qset (b.1.image ι) (b.2.image ι))
        rw [hι, qset_map, qset_map]
        exact ((Finset.disjoint_image (Sym2.map.injective hinj)).2 hab))
    obtain ⟨s', hs', hsz⟩ := hDis
    have hBc : HasCircuitSize n (fun x : Fin n → Bool => decide (∃ v ∈ B, x v = true))
        (B.card - 1) := bld_hasCircuitSize (bld_anyFinset B hB)
    have hlive : ∃ x : Fin n → Bool, decide (∃ v ∈ B, x v = true) = true := by
      obtain ⟨b, hb⟩ := hB
      exact ⟨fun _ => true, decide_eq_true ⟨b, hb, rfl⟩⟩
    obtain ⟨C, hC, hsz2, hev⟩ := Gap548Circuit.plug _ _ hBc hs' hlive
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
      have hsum : (L'.map (fun pb => (pb.1.card - 1) * (pb.2.card - 1))).sum
          = (L.map (fun pb => (pb.1.card - 1) * (pb.2.card - 1))).sum := by
        rw [hL', List.map_map]
        congr 1
        apply List.map_congr_left
        intro pb _
        simp only [Function.comp, Finset.card_image_of_injective _ hinj]
      rw [hsum] at hsz
      simp only [List.map_cons, List.sum_cons]
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
      · refine ⟨e0, (Finset.mem_sdiff.1 he0).1, fun v hv0 => ?_⟩
        rw [← yι]
        exact hv _ (by simp [Sym2.mem_map]; exact ⟨v, hv0, rfl⟩)
      · have hpx : x p = true := by rw [← yι]; exact hv _ (Sym2.mem_mk_left _ _)
        have hzx : decide (∃ v ∈ B, x v = true) = true := by
          rw [← yz]; exact hv _ (Sym2.mem_mk_right _ _)
        obtain ⟨b, hb, hbx⟩ := of_decide_eq_true hzx
        refine ⟨s(p, b), hQ0 (mem_qset hp hb), fun v hv0 => ?_⟩
        rcases Sym2.mem_iff.1 hv0 with rfl | rfl
        · exact hpx
        · exact hbx
    · rintro ⟨e, he, hv⟩
      by_cases hq : e ∈ Q
      · obtain ⟨⟨p, b⟩, hpb, rfl⟩ := Finset.mem_image.1 hq
        obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb
        have hpx : x p = true := hv p (Sym2.mem_mk_left _ _)
        have hbx : x b = true := hv b (Sym2.mem_mk_right _ _)
        refine ⟨s(ι p, z), by rw [hEp]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp),
          fun v hv0 => ?_⟩
        rcases Sym2.mem_iff.1 hv0 with rfl | rfl
        · exact (yι _).trans hpx
        · exact yz.trans (decide_eq_true ⟨b, hb, hbx⟩)
      · refine ⟨Sym2.map ι e, ?_, fun v hv0 => ?_⟩
        · rw [hEp, Finset.mem_union]
          exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨he, hq⟩))
        · obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hv0
          exact (yι w).trans (hv w hw)

open Classical in
/-- The iterated biclique bound for the edge function of a graph. -/
theorem biclique_family_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hG : ∃ i j : Fin n, G.Adj i j)
    (L : List (Finset (Fin n) × Finset (Fin n)))
    (hPT : ∀ pb ∈ L, pb.1 ⊆ T) (hdis : ∀ pb ∈ L, Disjoint pb.1 pb.2)
    (hP : ∀ pb ∈ L, pb.1.Nonempty) (hB : ∀ pb ∈ L, pb.2.Nonempty)
    (hadj : ∀ pb ∈ L, ∀ p ∈ pb.1, ∀ b ∈ pb.2, G.Adj p b)
    (hpw : L.Pairwise (fun a b => Disjoint (qset a.1 a.2) (qset b.1 b.2))) :
    ∃ s, HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s ∧
      s + 1 + (L.map (fun pb => (pb.1.card - 1) * (pb.2.card - 1))).sum
        ≤ G.edgeFinset.card + T.card := by
  obtain ⟨i0, j0, h0⟩ := hG
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hT a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  have hQE : ∀ pb ∈ L, qset pb.1 pb.2 ⊆ G.edgeFinset := by
    intro pb hpb e he
    obtain ⟨⟨p, b⟩, hpb', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hp, hb⟩ := Finset.mem_product.1 hpb'
    simpa using hadj pb hpb p hp b hb
  obtain ⟨s, hs, hsz⟩ := family_edges L.length n L rfl T G.edgeFinset hne cov hPT hdis hP hB hQE hpw
  obtain ⟨C, hC, hCs, hev⟩ := hs
  refine ⟨s, ⟨C, hC, hCs, fun x => ?_⟩, hsz⟩
  rw [hev x]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

end PEqualNP.MetaComplexity.EdgeFn.BicliqueFamily
