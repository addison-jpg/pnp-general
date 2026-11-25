import PEqualNP.MetaComplexity.Helpers.EdgeUpper
import PEqualNP.Outside.L_meta_548

/-!
# A 4-cycle saves a gate in the edge function

If `G` contains a 4-cycle `a - b - c - d - a` (as a subgraph) and `T` is a vertex cover, the edge
function of `G` has a fan-in two circuit with `|E| + |T| - 2` gates: one below the value
`|E| + tau - 1` that is exact on the window class (`EdgeFnWindow.lean`).

The cover holds an opposite pair of the cycle, say `a, c`. The circuit computes `z = x_b OR x_d`
once and uses it for both `a` and `c`: the edges `ab, ad, cb, cd` become `az, cz` on one more
input, the cover is unchanged, and `plug` (L-meta-548) substitutes `z`.
-/

namespace PEqualNP.MetaComplexity.EdgeFn.C4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.EdgeUpper

open Classical in
/-- The core: the 4-cycle `a b c d` with `a, c` in the cover. -/
theorem c4_core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (ha : a ∈ T) (hc : c ∈ T)
    (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 2) := by
  set ι : Fin n → Fin (n + 1) := Fin.castSucc
  set z : Fin (n + 1) := Fin.last n
  set Q : Finset (Sym2 (Fin n)) := {s(a, b), s(a, d), s(c, b), s(c, d)} with hQ
  set E0 := G.edgeFinset \ Q with hE0
  set Ep : Finset (Sym2 (Fin (n + 1))) :=
    E0.image (Sym2.map ι) ∪ {s(ι a, z), s(ι c, z)} with hEp
  set Tp : Finset (Fin (n + 1)) := T.image ι with hTp
  -- distinctness
  have hab' : a ≠ b := hab.ne
  have hcb : c ≠ b := hbc.ne.symm
  have had : a ≠ d := hda.ne.symm
  have hcd' : c ≠ d := hcd.ne
  have hQsub : Q ⊆ G.edgeFinset := by
    intro e he
    simp only [hQ, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp
    · exact hab
    · exact hda.symm
    · exact hbc.symm
    · exact hcd
  have hQcard : Q.card = 4 := by
    rw [hQ]
    have h1 : s(a, b) ∉ ({s(a, d), s(c, b), s(c, d)} : Finset _) := by
      simp [Sym2.eq_iff, hbd, hac, hab', hcb, had, hcd', hbd.symm, hac.symm, hab'.symm, hcb.symm, had.symm, hcd'.symm]
    have h2 : s(a, d) ∉ ({s(c, b), s(c, d)} : Finset _) := by
      simp [Sym2.eq_iff, hbd, hac, hab', hcb, had, hcd', hbd.symm, hac.symm, hab'.symm, hcb.symm, had.symm, hcd'.symm]
    have h3 : s(c, b) ∉ ({s(c, d)} : Finset _) := by
      simp [Sym2.eq_iff, hbd, hac, hab', hcb, had, hcd', hbd.symm, hac.symm, hab'.symm, hcb.symm, had.symm, hcd'.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hE0card : E0.card + 4 = G.edgeFinset.card := by
    rw [hE0, Finset.card_sdiff_of_subset hQsub, hQcard]
    have := Finset.card_le_card hQsub
    omega
  have hEpcard : Ep.card + 2 ≤ G.edgeFinset.card := by
    have h1 := Finset.card_union_le (E0.image (Sym2.map ι)) {s(ι a, z), s(ι c, z)}
    have h2 := Finset.card_image_le (s := E0) (f := Sym2.map ι)
    have h3 : ({s(ι a, z), s(ι c, z)} : Finset (Sym2 (Fin (n + 1)))).card ≤ 2 :=
      Finset.card_le_two
    rw [hEp]
    omega
  have hTpcard : Tp.card = T.card := Finset.card_image_of_injective _ (Fin.castSucc_injective n)
  have hEpne : Ep.Nonempty := ⟨s(ι a, z), by simp [hEp]⟩
  have hcov : ∀ e ∈ Ep, ∃ t ∈ Tp, t ∈ e := by
    intro e he
    rw [hEp, Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨e0, he0, rfl⟩ | he
    · revert he0
      refine Sym2.ind (fun i j => ?_) e0
      intro he0
      have hij : G.Adj i j := by
        have := (Finset.mem_sdiff.1 he0).1
        simpa using this
      rcases hT i j hij with h | h
      · exact ⟨ι i, Finset.mem_image_of_mem _ h, by simp⟩
      · exact ⟨ι j, Finset.mem_image_of_mem _ h, by simp⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact ⟨ι a, Finset.mem_image_of_mem _ ha, Sym2.mem_mk_left _ _⟩
      · exact ⟨ι c, Finset.mem_image_of_mem _ hc, Sym2.mem_mk_left _ _⟩
  have hH := bld_hasCircuitSize (bld_edges (n + 1) Tp Ep hEpne hcov)
  -- `z = x_b OR x_d` with one gate
  have hB : HasCircuitSize n (fun x : Fin n → Bool => x b || x d) 1 :=
    bld_hasCircuitSize (bld_or (bld_var b) (bld_var d))
  have hP := Gap548Circuit.plug (fun x : Fin n → Bool => x b || x d) _ hB hH
    ⟨fun _ => true, by simp⟩
  obtain ⟨C, hC, hsz, hev⟩ := hP
  refine ⟨C, hC, ?_, fun x => ?_⟩
  · rw [hTpcard] at hsz
    omega
  rw [hev x]
  -- the semantics
  set y : Fin (n + 1) → Bool := Fin.snoc x (x b || x d) with hy
  have yι : ∀ i, y (ι i) = x i := fun i => by simp [hy, ι]
  have yz : y z = (x b || x d) := by simp [hy, z]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, hv⟩
    rw [hEp, Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨e0, he0, rfl⟩ | he
    · revert he0 hv
      refine Sym2.ind (fun i j => ?_) e0
      intro he0 hv
      have hij : G.Adj i j := by
        have := (Finset.mem_sdiff.1 he0).1
        simpa using this
      refine ⟨i, j, hij, ?_, ?_⟩
      · rw [← yι]; exact hv _ (by simp)
      · rw [← yι]; exact hv _ (by simp)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      have key : ∀ u, G.Adj u b → G.Adj u d → (∀ v ∈ s(ι u, z), y v = true) →
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
        intro u hub hud hv
        have hu : x u = true := by rw [← yι]; exact hv _ (Sym2.mem_mk_left _ _)
        have hz : (x b || x d) = true := by rw [← yz]; exact hv _ (Sym2.mem_mk_right _ _)
        rcases Bool.or_eq_true_iff.1 hz with h | h
        · exact ⟨u, b, hub, hu, h⟩
        · exact ⟨u, d, hud, hu, h⟩
      rcases he with rfl | rfl
      · exact key a hab hda.symm hv
      · exact key c hbc.symm hcd hv
  · rintro ⟨i, j, hij, hi, hj⟩
    by_cases hq : s(i, j) ∈ Q
    · -- an edge of the cycle: through `z`
      have hzt : y z = true := by
        rw [yz]
        simp only [hQ, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hq
        rcases hq with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
            (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hi, hj]
      have hend : (x a = true ∧ s(ι a, z) ∈ Ep) ∨ (x c = true ∧ s(ι c, z) ∈ Ep) := by
        simp only [hQ, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hq
        rcases hq with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
            (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hEp, hi, hj]
      rcases hend with ⟨hx, hm⟩ | ⟨hx, hm⟩
      · refine ⟨_, hm, fun v hv => ?_⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact (yι _).trans hx
        · exact hzt
      · refine ⟨_, hm, fun v hv => ?_⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact (yι _).trans hx
        · exact hzt
    · refine ⟨Sym2.map ι s(i, j), ?_, fun v hv => ?_⟩
      · rw [hEp, Finset.mem_union]
        left
        exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨by simpa using hij, hq⟩)
      · simp only [Sym2.map_mk, Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact (yι _).trans hi
        · exact (yι _).trans hj

/-- A 4-cycle saves a gate: if `G` has a 4-cycle `a - b - c - d - a` (as a subgraph) and `T` is a
vertex cover, the edge function has a fan-in two circuit with `|E| + |T| - 2` gates. -/
theorem c4_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 2) := by
  by_cases h : a ∈ T ∧ c ∈ T
  · exact c4_core n G T a b c d hab hbc hcd hda hac hbd h.1 h.2 hT
  · have hb : b ∈ T ∧ d ∈ T := by
      rcases not_and_or.1 h with h | h
      · exact ⟨(hT a b hab).resolve_left h, (hT d a hda).resolve_right h⟩
      · exact ⟨(hT b c hbc).resolve_right h, (hT c d hcd).resolve_left h⟩
    exact c4_core n G T b c d a hbc hcd hda hab hbd hac.symm hb.1 hb.2 hT

/-- Exactness forces no 4-cycle: if every circuit for the edge function has at least
`|E| + |T| - 1` gates for a vertex cover `T`, then `G` has no 4-cycle as a subgraph. -/
theorem c4_free_of_exact (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hlb : ∀ s, HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
      G.edgeFinset.card + T.card ≤ s + 1) :
    ¬ ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ a ≠ c ∧ b ≠ d := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd⟩
  have h := hlb _ (c4_upper n G T a b c d hab hbc hcd hda hac hbd hT)
  have ha : a ∈ T ∨ b ∈ T := hT a b hab
  have hc : c ∈ T ∨ d ∈ T := hT c d hcd
  have h2 : 2 ≤ T.card := by
    have hne : ∀ u v, u ∈ T → v ∈ T → u ≠ v → 2 ≤ T.card := fun u v hu hv huv =>
      Finset.one_lt_card.2 ⟨u, hu, v, hv, huv⟩
    rcases ha with ha | ha <;> rcases hc with hc | hc
    · exact hne a c ha hc hac
    · exact hne a d ha hc hda.ne.symm
    · exact hne b c ha hc hbc.ne
    · exact hne b d ha hc hbd
  omega

end PEqualNP.MetaComplexity.EdgeFn.C4
