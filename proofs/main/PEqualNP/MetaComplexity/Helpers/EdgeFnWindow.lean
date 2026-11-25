import PEqualNP.MetaComplexity.Helpers.EdgeFnFinal
import PEqualNP.MetaComplexity.Helpers.ForestGraph
import PEqualNP.MetaComplexity.Helpers.NotFreeCor

/-!
# The edge-function lower bound on the window class

The class `W6`: every cycle has length at least 6 and has six cyclically consecutive vertices,
each with at most two neighbours in the whole graph (a "window").

* `w6_hered`: `W6` is closed under `delV` (a cycle of `delV G X` is a cycle of `G`, with the same
  vertices, and degrees only drop).
* `w6_dich`: a graph of `W6` with an edge has a good leaf (it is a forest) or a run (the window of
  any cycle is a run).
* `w6_lb`: the bound `|A| + |E| + k ≤ s + 1` of `StmtLB` on `W6`, from `a1_of_pieces`.

`W6` contains every forest and every graph of the class `T7` of `StmtLB` (`t7_w6`), and graphs
where two vertices of degree at least 3 are adjacent, so `w6_lb` contains both the forest bound
(L-meta-104, here with free OR-inputs added) and the class bound (L-meta-204). With the upper bound
(L-meta-105) it gives the exact size `|E| + tau - 1` on `W6` (`w6_exact`), and with L-meta-154 a
smallest circuit with no NOT gate (`w6_not_free`, the form of L-meta-113 on `W6`).
-/

namespace PEqualNP.MetaComplexity.EdgeFn.Window

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-- The window class: every cycle has length at least 6 and six cyclically consecutive vertices
with at most two neighbours each. -/
def W6 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length ∧
    ∃ i : ℕ, ∀ j : ℕ, j < 6 → (G.neighborSet (c.getVert ((i + j) % c.length))).ncard ≤ 2

/-! ## Heredity -/

theorem w6_hered : Hered (fun _ G => W6 G) := by
  intro n G X hW v c hc
  have hle := delV_le G X
  obtain ⟨h6, i, hi⟩ := hW v (c.mapLe hle) (hc.mapLe hle)
  rw [Walk.length_mapLe] at h6 hi
  refine ⟨h6, i, fun j hj => ?_⟩
  have := hi j hj
  rw [Walk.mapLe, Walk.getVert_map] at this
  have hsub : ∀ w, (delV G X).neighborSet w ⊆ G.neighborSet w := fun w y hy => hle hy
  exact le_trans (Set.ncard_le_ncard (hsub _) (Set.toFinite _)) this

/-! ## The dichotomy -/

/-- At most two neighbours, two distinct known ones: they are all. -/
theorem nb_two {n : ℕ} {G : SimpleGraph (Fin n)} {v a b : Fin n}
    (h : (G.neighborSet v).ncard ≤ 2) (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) :
    ∀ w, G.Adj v w → w = a ∨ w = b := by
  intro w hw
  by_contra hne
  push Not at hne
  have hsub : ({a, b, w} : Set (Fin n)) ⊆ G.neighborSet v := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hw
  have h3 : ({a, b, w} : Set (Fin n)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨a, b, w, hab, hne.1.symm, hne.2.symm, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- At most two neighbours, one known: some `c` names the rest. -/
theorem nb_end {n : ℕ} {G : SimpleGraph (Fin n)} {v a : Fin n}
    (h : (G.neighborSet v).ncard ≤ 2) (ha : G.Adj v a) :
    ∃ c, ∀ w, G.Adj v w → w = a ∨ w = c := by
  by_cases hex : ∃ c, c ≠ a ∧ G.Adj v c
  · obtain ⟨c, hca, hc⟩ := hex
    exact ⟨c, nb_two h ha hc (Ne.symm hca)⟩
  · push Not at hex
    exact ⟨a, fun w hw => by
      by_cases hwa : w = a
      · exact Or.inl hwa
      · exact absurd hw (hex w hwa)⟩

/-- Consecutive positions on a cycle, read modulo its length, are adjacent. -/
theorem cyc_adj {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v)
    (hL0 : 0 < c.length) (i j : ℕ) :
    G.Adj (c.getVert ((i + j) % c.length)) (c.getVert ((i + (j + 1)) % c.length)) := by
  set L := c.length with hL
  have hk : (i + j) % L < L := Nat.mod_lt _ hL0
  have := c.adj_getVert_succ hk
  have he : c.getVert ((i + j) % L + 1) = c.getVert ((i + (j + 1)) % L) := by
    by_cases hlt : (i + j) % L + 1 < L
    · congr 1
      have e1 := Nat.mod_add_mod (i + j) L 1
      rw [Nat.mod_eq_of_lt hlt] at e1
      rw [e1, add_assoc]
    · have heq : (i + j) % L + 1 = L := by omega
      rw [heq, Walk.getVert_length]
      have h0 : (i + (j + 1)) % L = 0 := by
        have e1 := Nat.mod_add_mod (i + j) L 1
        rw [heq, Nat.mod_self] at e1
        rw [← add_assoc, ← e1]
      rw [h0, Walk.getVert_zero]
  rw [he] at this
  exact this

/-- Two positions less than `L` apart have different residues modulo `L`. -/
theorem mod_ne (L i j j' : ℕ) (hlt : j < j') (hd : j' < j + L) : (i + j) % L ≠ (i + j') % L := by
  intro hmod
  have hd' := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  obtain ⟨q, hq⟩ := hd'
  rcases q with _ | q
  · omega
  · have : L * (q + 1) ≥ L := Nat.le_mul_of_pos_right L (by omega)
    omega

/-- Positions on a cycle with different residues are different vertices. -/
theorem cyc_ne {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} {c : G.Walk v v} (hc : c.IsCycle)
    {i j : ℕ} (hij : i % c.length ≠ j % c.length) : c.getVert (i % c.length) ≠ c.getVert (j % c.length) := by
  have hL0 : 0 < c.length := by have := hc.three_le_length; omega
  have hm : ∀ m, m % c.length ≤ c.length - 1 := fun m => by
    have := Nat.mod_lt m hL0
    omega
  exact fun heq => hij (hc.getVert_injOn' (by simpa using hm i) (by simpa using hm j) heq)

/-- Walking `d` steps along a cycle. -/
theorem cyc_walk {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v)
    (hL0 : 0 < c.length) (i : ℕ) : ∀ d : ℕ,
    ∃ p : G.Walk (c.getVert ((i + 0) % c.length)) (c.getVert ((i + d) % c.length)), p.length = d
  | 0 => ⟨Walk.nil, rfl⟩
  | d + 1 => by
    obtain ⟨p, hp⟩ := cyc_walk c hL0 i d
    exact ⟨p.concat (cyc_adj c hL0 i d), by rw [Walk.length_concat, hp]⟩

/-- The window of a cycle is a run. -/
theorem run_of_window {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v)
    (hc : c.IsCycle) (h6 : 6 ≤ c.length) (i : ℕ)
    (hi : ∀ j : ℕ, j < 6 → (G.neighborSet (c.getVert ((i + j) % c.length))).ncard ≤ 2) :
    ∃ a' a s t b b' : Fin n, Run G a' a s t b b' := by
  set L := c.length with hL
  have hL0 : 0 < L := by omega
  let f : ℕ → Fin n := fun j => c.getVert ((i + j) % L)
  have adj : ∀ j, G.Adj (f j) (f (j + 1)) := fun j => cyc_adj c hL0 i j
  have ne : ∀ j j', j < 6 → j' < 6 → j ≠ j' → f j ≠ f j' := by
    intro j j' hj hj' hjj'
    have hmod : (i + j) % L ≠ (i + j') % L := by
      rcases Nat.lt_or_gt_of_ne hjj' with hlt | hlt
      · exact mod_ne L i j j' hlt (by omega)
      · exact fun h => mod_ne L i j' j hlt (by omega) h.symm
    have := cyc_ne hc (i := i + j) (j := i + j') (by simpa [Nat.mod_mod] using hmod)
    simpa [Nat.mod_mod] using this
  have inner : ∀ j, 1 ≤ j → j ≤ 4 → ∀ w, G.Adj (f j) w ↔ w = f (j - 1) ∨ w = f (j + 1) := by
    intro j h1 h4 w
    have hprev : G.Adj (f j) (f (j - 1)) := by
      have := adj (j - 1)
      rw [show j - 1 + 1 = j by omega] at this
      exact this.symm
    constructor
    · exact nb_two (hi j (by omega)) hprev (adj j) (ne (j - 1) (j + 1) (by omega) (by omega) (by omega))
        w
    · rintro (rfl | rfl)
      · exact hprev
      · exact adj j
  refine ⟨f 0, f 1, f 2, f 3, f 4, f 5, ⟨?_, inner 1 le_rfl (by norm_num), inner 2 (by norm_num)
    (by norm_num), inner 3 (by norm_num) (by norm_num), inner 4 (by norm_num) le_rfl, ?_, ?_⟩⟩
  · have hinj : Function.Injective (fun k : Fin 6 => f k) := fun k k' h => by
      by_contra hk
      exact ne k k' k.2 k'.2 (fun e => hk (Fin.ext e)) h
    have := List.nodup_ofFn.2 hinj
    simpa [List.ofFn_succ] using this
  · exact nb_end (hi 0 (by norm_num)) (adj 0)
  · obtain ⟨c', hc'⟩ := nb_end (hi 5 (by norm_num)) (adj 4).symm
    exact ⟨c', hc'⟩

theorem w6_dich : Dich (fun _ G => W6 G) := by
  intro n G hW hE
  by_cases hac : G.IsAcyclic
  · exact Or.inl (Forest.forest_good_leaf G hac hE)
  · rw [IsAcyclic] at hac
    push Not at hac
    obtain ⟨v, c, hc⟩ := hac
    obtain ⟨h6, i, hi⟩ := hW v c hc
    exact Or.inr (run_of_window c hc h6 i hi)

/-! ## The bound on `W6` -/

/-- The class form of the bound on `W6`. -/
theorem w6_a1 : StmtA1 (fun _ G => W6 G) :=
  a1_of_pieces w6_hered w6_dich stmtG3 stmtG6 stmtML_final Res.ToolRes0_proof Res.ToolRes1_proof
    Res.ToolDrop0_proof Res.ToolDrop1_proof

/-- The lower bound on the window class: for `G` in `W6`, `A` a set of inputs that no edge meets,
and `k` at most every vertex cover, every fan-in two circuit over AND, OR, NOT (every gate counted)
for "some input of `A` is true, or both ends of some edge are true" has at least
`|A| + |E| + k - 1` gates. -/
theorem w6_lb : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), W6 G →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s →
    A.card + G.edgeSet.ncard + k ≤ s + 1 := by
  intro n k s G A hW hinv hk hC
  have hb := w6_a1 n G A hW hinv s hC
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  have := hk T hT
  unfold Phi1 at hb
  omega

/-! ## `T7` and forests are in `W6` -/

theorem forest_w6 {n : ℕ} (G : SimpleGraph (Fin n)) (h : G.IsAcyclic) : W6 G :=
  fun _ c hc => absurd hc (h c)

/-- The class `T7` of L-meta-204 is contained in `W6`. -/
theorem t7_w6 {n : ℕ} (G : SimpleGraph (Fin n)) (hT : T7 G) : W6 G := by
  intro v c hc
  set L := c.length with hL
  have h7 : 7 ≤ L := hT.1 v c hc
  refine ⟨by omega, ?_⟩
  have hL0 : 0 < L := by omega
  -- the vertices of `c` with at least three neighbours
  by_cases hhub : ∃ m, m < L ∧ 3 ≤ (G.neighborSet (c.getVert m)).ncard
  · obtain ⟨m, hmL, hm⟩ := hhub
    refine ⟨m + 1, fun j hj => ?_⟩
    by_contra hbig
    push Not at hbig
    have hm0 : (m + 0) % L = m := by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt hmL
    have hne : (m + 0) % L ≠ (m + (j + 1)) % L := mod_ne L m 0 (j + 1) (by omega) (by omega)
    obtain ⟨p, hp⟩ := cyc_walk c hL0 m (j + 1)
    have hv := cyc_ne hc (i := m + 0) (j := m + (j + 1)) (by simpa [Nat.mod_mod] using hne)
    have h3 : 3 ≤ (G.neighborSet (c.getVert ((m + (j + 1)) % L))).ncard := by
      rw [show m + (j + 1) = m + 1 + j by omega]; omega
    have := hT.2 _ _ hv (by rw [hm0]; exact hm) h3 p
    omega
  · push Not at hhub
    refine ⟨0, fun j hj => ?_⟩
    have := hhub ((0 + j) % L) (Nat.mod_lt _ (by omega))
    omega

/-! ## Consequences on `W6`: exact size, monotone circuits, NOT gates -/

/-- The edge function alone, in the form of L-meta-104 and L-meta-105, has circuits of size `s`
only above the bound. -/
theorem w6_lb0 (n s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hW : W6 G)
    (T : Finset (Fin n)) (hmin : ∀ T' : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card)
    (hC : HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) :
    G.edgeFinset.card + T.card ≤ s + 1 := by
  have hC' : HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s := by
    obtain ⟨C, hC, hs, hev⟩ := hC
    refine ⟨C, hC, hs, fun x => ?_⟩
    rw [hev x]
    simp
  have := w6_lb n T.card s G ∅ hW (fun i j _ => Finset.notMem_empty i) hmin hC'
  have hec : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hec, Finset.card_empty] at this
  omega

/-- The exact size on `W6`: for `G` in `W6` with an edge and `T` a least vertex cover, the edge
function has a fan-in two circuit with `s` gates exactly when `|E| + |T| ≤ s + 1`. -/
theorem w6_exact (n s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hW : W6 G)
    (hE : ∃ i j : Fin n, G.Adj i j) (T : Finset (Fin n))
    (hT : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hmin : ∀ T' : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card) :
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s ↔
    G.edgeFinset.card + T.card ≤ s + 1 := by
  refine ⟨w6_lb0 n s G hW T hmin, fun hs => ?_⟩
  obtain ⟨D, hD, -, hDfun, hDsize⟩ := Helpers.NotFreeCor.nfc_edge_upper_mono n G T hE hT
  exact ⟨D, hD, by omega, fun x => congrFun hDfun x⟩

/-- Monotone circuits on `W6` (the form of L-meta-115): every fan-in two circuit with no NOT gate
for the edge function has at least `|E| + |T| - 1` gates for some vertex cover `T`. -/
theorem w6_mono (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hW : W6 G)
    (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : FanInTwo D)
    (hfun : circuitFun n D =
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))) :
    ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      G.edgeFinset.card + T.card ≤ D.size + 1 := by
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  have hmin : ∀ T' : Finset (Fin n),
      (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := fun T' hT' =>
    hTc ▸ tau_le G T' hT'
  exact ⟨T, hT, w6_lb0 n D.size G hW T hmin ⟨D, hD, le_rfl, fun x => congrFun hfun x⟩⟩

/-- NOT gates never save a gate on `W6` (the form of L-meta-113): every fan-in two circuit for the
edge function has an equivalent one with no NOT gate and no more gates. -/
theorem w6_not_free (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hW : W6 G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : FanInTwo C)
    (hfun : circuitFun n C =
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, FanInTwo D ∧
      (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      circuitFun n D = circuitFun n C ∧ D.size ≤ C.size := by
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · obtain ⟨T, hT, hTc⟩ := tau_attained G
    have hmin : ∀ T' : Finset (Fin n),
        (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := fun T' hT' =>
      hTc ▸ tau_le G T' hT'
    have hlb := w6_lb0 n C.size G hW T hmin ⟨C, hC, le_rfl, fun x => congrFun hfun x⟩
    obtain ⟨D, hD, hDnot, hDfun, hDsize⟩ := Helpers.NotFreeCor.nfc_edge_upper_mono n G T hE hT
    exact ⟨D, hD, hDnot, hDfun.trans hfun.symm, by omega⟩
  · refine ⟨⟨[], n⟩, by simp [FanInTwo], by simp, ?_, by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩
    rw [hfun]
    funext x
    simp only [circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil]
    have : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true :=
      fun ⟨i, j, h, _⟩ => hE ⟨i, j, h⟩
    simp [this]

end PEqualNP.MetaComplexity.EdgeFn.Window
