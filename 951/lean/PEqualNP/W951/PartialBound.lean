import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.Frame
import PEqualNP.W951.TwoWorld

/-! Partial bound for one NOT gate whose input covers, once `x k = true`, every output whose set
avoids the variable `k`. The sets avoiding `k` are counted in the monotone circuit `C0 gates`
(NOT := false) with zero point `Zof (S w)` and test points `e_u ∨ e_k`; the counted wires are
pairwise disjoint and never the NOT position, which gives the `+ 1`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

theorem constNot_id (b : GateOp) (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    constNot b g = g := by
  obtain ⟨op, ins⟩ := g
  simp only at h
  rcases h with rfl | rfl <;> rfl

theorem mem_DT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (i : ℕ) :
    i ∈ DT z p R gs ↔ i ∈ Finset.Ico n (n + gs.length) ∧ CntT z p R gs i := by
  classical
  unfold DT
  rw [Finset.mem_filter]

/-- Swapping one gate for another with the same value at `x` changes no wire at `x`. -/
theorem val_swap {n : ℕ} (A B : List Gate) (g g' : Gate) (x : Fin n → Bool)
    (h : g.op.eval (g.inputs.map fun j => val A x j) =
      g'.op.eval (g'.inputs.map fun j => val A x j)) :
    ∀ i, val (A ++ g :: B) x i = val (A ++ g' :: B) x i := by
  induction B using List.reverseRecOn with
  | nil =>
    intro i
    rw [val_snoc, val_snoc, h]
  | append_singleton B b ih =>
    intro i
    have e1 : A ++ g :: (B ++ [b]) = (A ++ g :: B) ++ [b] := by simp
    have e2 : A ++ g' :: (B ++ [b]) = (A ++ g' :: B) ++ [b] := by simp
    rw [e1, e2, val_snoc, val_snoc]
    have hl : (A ++ g :: B).length = (A ++ g' :: B).length := by simp
    rw [hl, ih i]
    have hm : (b.inputs.map fun j => val (A ++ g :: B) x j) =
        b.inputs.map fun j => val (A ++ g' :: B) x j :=
      List.map_congr_left fun j _ => ih j
    rw [hm]

/-- Decomposed form of `partial_bound`. -/
theorem partial_bound_core {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (A B : List Gate) (hw : ℕ) (out : Fin m → ℕ)
    (hA : ∀ g ∈ A, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hB : ∀ g ∈ B, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwlt : hw < n + A.length)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val (A ++ ⟨GateOp.not, [hw]⟩ :: B) x (out w) = decide (∃ v ∈ S w, x v = true))
    (k : Fin n)
    (hk : ∀ w, k ∉ S w → ∀ x : Fin n → Bool, x k = true →
      val (A ++ ⟨GateOp.not, [hw]⟩ :: B) x (out w) = true →
      val (A ++ ⟨GateOp.not, [hw]⟩ :: B) x hw = true) :
    1 + ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), ((S w).card - 1) ≤
      (A ++ ⟨GateOp.not, [hw]⟩ :: B).length := by
  classical
  set gates : List Gate := A ++ ⟨GateOp.not, [hw]⟩ :: B with hgates
  set G0 : List Gate := A ++ ⟨GateOp.or, []⟩ :: B with hG0
  have hlen : G0.length = gates.length := by simp [hG0, hgates]
  have hC0 : C0 gates = G0 := by
    have ha : A.map (constNot GateOp.or) = A := by
      conv_rhs => rw [← List.map_id A]
      exact List.map_congr_left fun g hg => constNot_id _ g (hA g hg).1
    have hb : B.map (constNot GateOp.or) = B := by
      conv_rhs => rw [← List.map_id B]
      exact List.map_congr_left fun g hg => constNot_id _ g (hB g hg).1
    simp only [C0, hgates, hG0, List.map_append, List.map_cons, ha, hb]
    rfl
  have hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    simp only [hgates, List.mem_append, List.mem_cons] at hg
    rcases hg with h | rfl | h
    · rcases (hA g h).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
    · rcases (hB g h).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have h0 : ∀ g ∈ G0, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simp only [hG0, List.mem_append, List.mem_cons] at hg
    rcases hg with h | rfl | h
    · exact hA g h
    · exact ⟨Or.inr rfl, by simp⟩
    · exact hB g h
  -- C0 below real
  have low : ∀ (x : Fin n → Bool) i, val G0 x i = true → val gates x i = true := by
    intro x i h
    rw [← hC0] at h
    exact ((sandwich gates hops x) i).1 h
  -- agreement when the NOT input is true
  have agree : ∀ (x : Fin n → Bool), val gates x hw = true → ∀ i, val gates x i = val G0 x i := by
    intro x hx
    have hAx : val A x hw = true := by
      rw [← val_append A (⟨GateOp.not, [hw]⟩ :: B) x hw hwlt]
      exact hx
    exact val_swap A B _ _ x (by simp [GateOp.eval, hAx])
  -- the NOT position is false in G0
  have hpos : ∀ x : Fin n → Bool, val G0 x (n + A.length) = false := by
    intro x
    have e : G0 = (A ++ [⟨GateOp.or, []⟩]) ++ B := by simp [hG0]
    rw [e, val_append _ _ _ _ (by simp), val_snoc, if_pos (by simp)]
    simp [GateOp.eval]
  have mono := fun (x y : Fin n → Bool) => mono_val G0 (fun g hg => (h0 g hg).1) x y
  let pt : Fin n → Fin n → Bool := fun u c => decide (c = u ∨ c = k)
  let Dw : Fin m → Finset ℕ := fun w => DT (Zof (S w)) pt (S w) G0
  have hgoodT : ∀ w, GoodT (Zof (S w)) pt (S w) G0 := by
    intro w pre g rest h
    exact Or.inl (h0 g (by rw [h]; simp))
  have hbound : ∀ w, k ∉ S w → (S w).card - 1 ≤ (Dw w).card := by
    intro w hkw
    refine countT_bound (Zof (S w)) pt (S w) ?_ G0 (hgoodT w) (out w) ?_ ?_
    · intro u _ c hc hz
      simp only [pt, decide_eq_true_eq] at hc
      simp only [Zof, decide_eq_false_iff_not, not_not] at hz
      rcases hc with h | h
      · exact h
      · exact absurd (h ▸ hz) hkw
    · cases hc : val G0 (Zof (S w)) (out w)
      · rfl
      · have := low _ _ hc
        rw [zero_of_sub S S gates out hev (fun _ => subset_rfl) w] at this
        exact absurd this (by simp)
    · intro u hu
      have hreal : val gates (pt u) (out w) = true := by
        rw [hev]
        simp only [decide_eq_true_eq]
        exact ⟨u, hu, by simp [pt]⟩
      have hh := hk w hkw (pt u) (by simp [pt]) hreal
      rw [← agree (pt u) hh]
      exact hreal
  have hdisj : ∀ a ∈ Finset.univ.filter (fun w => k ∉ S w),
      ∀ b ∈ Finset.univ.filter (fun w => k ∉ S w), a ≠ b → Disjoint (Dw a) (Dw b) := by
    intro a _ b hb hab
    have hkb : k ∉ S b := (Finset.mem_filter.mp hb).2
    rw [Finset.disjoint_left]
    intro i hia hib
    replace hia := (mem_DT _ _ _ _ _).mp hia
    replace hib := (mem_DT _ _ _ _ _).mp hib
    obtain ⟨-, -, u, v, huv, hu, hv, h1, h2⟩ := hia
    have hzb := hib.2.1
    have inb : ∀ c ∈ S a, val G0 (pt c) i = true → c ∈ S b := by
      intro c _ hc
      by_contra hcb
      have := mono (pt c) (Zof (S b)) (by
        intro d hd
        simp only [pt, decide_eq_true_eq] at hd
        simp only [Zof, decide_eq_true_eq]
        rcases hd with rfl | rfl
        · exact hcb
        · exact hkb) i hc
      rw [hzb] at this
      exact absurd this (by simp)
    have := pair_card (S a) (S b) u v huv (Finset.mem_inter.mpr ⟨hu, inb u hu h1⟩)
      (Finset.mem_inter.mpr ⟨hv, inb v hv h2⟩)
    have := hS a b hab
    omega
  have hsub : ∀ w ∈ Finset.univ.filter (fun w => k ∉ S w),
      Dw w ⊆ (Finset.Ico n (n + gates.length)).erase (n + A.length) := by
    intro w _ i hw'
    replace hw' := (mem_DT _ _ _ _ _).mp hw'
    obtain ⟨hI, -, u, -, -, -, -, h1, -⟩ := hw'
    rw [hlen] at hI
    refine Finset.mem_erase.mpr ⟨?_, hI⟩
    rintro rfl
    rw [hpos] at h1
    exact absurd h1 (by simp)
  have hmem : n + A.length ∈ Finset.Ico n (n + gates.length) := by
    simp [hgates]
  have hcard : ((Finset.Ico n (n + gates.length)).erase (n + A.length)).card + 1 =
      gates.length := by
    rw [Finset.card_erase_add_one hmem]
    simp
  have hsum : ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), ((S w).card - 1) ≤
      ((Finset.Ico n (n + gates.length)).erase (n + A.length)).card :=
    calc ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), ((S w).card - 1)
        ≤ ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), (Dw w).card :=
          Finset.sum_le_sum fun w hw' => hbound w (Finset.mem_filter.mp hw').2
      _ ≤ _ := PEqualNP.Base.Matching.sum_card_le_of_pairwiseDisjoint _ _ _ hdisj hsub
  omega

/-- One NOT gate at index `p` with input wire `hw`; once `x k = true`, the wire `hw` covers every
output whose set avoids `k`. Then the sets avoiding `k` alone already force
`1 + ∑ (|S w| - 1)` gates. -/
theorem partial_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (p hw : ℕ) (hp : p < gates.length)
    (hnot : gates[p] = ⟨GateOp.not, [hw]⟩) (hwlt : hw < n + p)
    (hother : ∀ (i : ℕ) (hi : i < gates.length), i ≠ p →
      gates[i].op = GateOp.and ∨ gates[i].op = GateOp.or)
    (k : Fin n)
    (hk : ∀ w, k ∉ S w → ∀ x : Fin n → Bool, x k = true →
      val gates x (out w) = true → val gates x hw = true) :
    1 + ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), ((S w).card - 1) ≤ gates.length := by
  have hsplit : gates = gates.take p ++ ⟨GateOp.not, [hw]⟩ :: gates.drop (p + 1) := by
    rw [← hnot, ← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have hlt : (gates.take p).length = p := by
    rw [List.length_take]; omega
  have hA : ∀ g ∈ gates.take p, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hgm
    rw [List.getElem_take]
    rw [hlt] at hi
    exact ⟨hother i (by omega) (by omega), (hg _ (List.getElem_mem _)).2⟩
  have hB : ∀ g ∈ gates.drop (p + 1),
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hgm
    rw [List.getElem_drop]
    rw [List.length_drop] at hi
    exact ⟨hother (p + 1 + i) (by omega) (by omega), (hg _ (List.getElem_mem _)).2⟩
  have := partial_bound_core S hS (gates.take p) (gates.drop (p + 1)) hw out hA hB
    (by rw [hlt]; exact hwlt) (by rw [← hsplit]; exact hev) k (by rw [← hsplit]; exact hk)
  rwa [← hsplit] at this

end PEqualNP.Outside.L_meta_951_aux
