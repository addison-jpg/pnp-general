import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2Induct
import PEqualNP.W951.MergeSDR

/-!
# F2Desc: front A2's F2-step lemmas F1 and F2-desc (refereed CORRECT, dwV8p 12:56)

* **F2-desc** (`sep_descend`): a wire with a real separating triple (`0` at `Z`, `1` at `Z + e_u` and
  `Z + e_u'`, `u ≠ u'`) descends through AND gates (to an input that is `0` at `Z`) to an OR gate with
  the same triple; inputs and the NOT gate never separate (the NOT gate is antitone). Consequences:
  `exists_F2_of_sep` (a separating wire for an alive set above `Q` gives an `F2(Q)` gate),
  `F2_nonempty_of_alive` (the outputs: every alive set with two points gives an `F2(Q)` gate),
  `mergeSet_subset_F2` (every real merge gate at a zero point `Z ⊇ Q` avoiding an alive set lies in
  `F2(Q)`), **`muF2_of_mergeSDR`** (MergeSDR ⇒ MU over F2; no NOT position needed).
* **F1** (`F1_real_zero`): for `v` heavy over `Q` (`h(Q ∪ {v}) = 1`), every real witness with `Q ∪ {v}`
  fixed to `1` has its gate `0` at `Q ∪ {v}` (above `Q ∪ {v}` the NOT gate is `0`, the real circuit is
  `C_0`, monotone). So `card_real_le_gainF2`: the `F2(Q)` gates that are `1` at `Q ∪ {v}` leave F2 under
  `x_v := 1` (false for light `v`, as front says).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section F2Desc

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **F2-desc**: a real separating triple descends to an OR gate with the same triple. -/
theorem sep_descend (Z : Fin n → Bool) {u u' : Fin n} (huu : u ≠ u') :
    ∀ i, val gates Z i = false → val gates (Function.update Z u true) i = true →
      val gates (Function.update Z u' true) i = true →
      ∃ k, IsOrAt gates k ∧ val gates Z (n + k) = false ∧
        val gates (Function.update Z u true) (n + k) = true ∧
        val gates (Function.update Z u' true) (n + k) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro h0 h1 h2
  by_cases hin : i < n
  · rw [val_input gates Z i hin] at h0
    rw [val_input gates _ i hin] at h1 h2
    have e1 : (⟨i, hin⟩ : Fin n) = u := by
      by_contra h
      rw [Function.update_of_ne h, h0] at h1
      exact absurd h1 (by decide)
    have e2 : (⟨i, hin⟩ : Fin n) = u' := by
      by_contra h
      rw [Function.update_of_ne h, h0] at h2
      exact absurd h2 (by decide)
    exact absurd (e1.symm.trans e2) huu
  by_cases hil : n + gates.length ≤ i
  · rw [mr_val_ge gates _ i hil] at h1
    exact absurd h1 (by decide)
  obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
  have hk : k < gates.length := by omega
  rcases (hg _ (List.getElem_mem hk)).1 with hop | hop | hop
  · rw [mr_val_gate gates Z k hk, hop] at h0
    rw [mr_val_gate gates _ k hk, hop] at h1 h2
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id] at h0 h1 h2
    obtain ⟨a, ha, haz⟩ := h0
    have hua := h1 a ha
    have hva := h2 a ha
    have ha' : a < n + k := by
      by_contra h
      rw [mr_val_ge (gates.take k) _ a (by simp; omega)] at hua
      exact absurd hua (by simp)
    rw [← mr_val_take gates _ k a ha'] at hua hva
    have haz' : val gates Z a = false := by
      rw [mr_val_take gates _ k a ha']
      simpa using haz
    exact ih a ha' haz' hua hva
  · exact ⟨k, ⟨gates[k], List.getElem?_eq_getElem hk, hop⟩, h0, h1, h2⟩
  · have hkp : k = p := hU k p hk hp hop hN
    rw [hkp] at h0 h1
    have := not_false_of_le gates p hp hg hU hN (le_upPt Z u) h0
    rw [upPt] at this
    rw [this] at h1
    exact absurd h1 (by decide)

include hg hU hN in
/-- **A separating wire for an alive set above `Q` gives an `F2(Q)` gate** (with the same triple). -/
theorem exists_F2_of_sep (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) {w : Fin m}
    (hw : w ∈ aliveSets S Q) (Z : Fin n → Bool) (hZR : ∀ x ∈ S w, Z x = false)
    (hZQ : ∀ x ∈ Q, Z x = true) {u u' : Fin n} (hu : u ∈ S w) (hu' : u' ∈ S w) (huu : u ≠ u')
    (i : ℕ) (h0 : val gates Z i = false) (h1 : val gates (Function.update Z u true) i = true)
    (h2 : val gates (Function.update Z u' true) i = true) :
    ∃ j ∈ F2 gates S Q, F2Wit gates (S w) Q j := by
  obtain ⟨k, hor, hk0, hk1, hk2⟩ := sep_descend gates p hp hg hU hN Z huu i h0 h1 h2
  have hwit : F2Wit gates (S w) Q (n + k) := ⟨Z, u, u', hu, hu', huu, hZR, hZQ, hk0, hk1, hk2⟩
  exact ⟨n + k, mem_F2.mpr ⟨⟨k, rfl, hor⟩, w, hw, hwit⟩, hwit⟩

include hg hU hN in
/-- **The outputs**: every set alive at `Q` with two points has an `F2(Q)` gate (descend from its
output at `Z = Q`). -/
theorem F2_nonempty_of_alive (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) {w : Fin m} (hw : w ∈ aliveSets S Q) (h2 : 2 ≤ (S w).card) :
    (F2 gates S Q).Nonempty := by
  obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.mp (by omega : 1 < (S w).card)
  have hQ := mem_aliveSets.mp hw
  have hZR : ∀ x ∈ S w, canonPt Q x = false := by
    intro x hx
    simp only [canonPt, decide_eq_false_iff_not]
    exact Finset.disjoint_left.mp hQ hx
  have hone : ∀ y ∈ S w, val gates (Function.update (canonPt Q) y true) (out w) = true := by
    intro y hy
    rw [hev]
    exact decide_eq_true ⟨y, hy, by simp⟩
  obtain ⟨j, hj, -⟩ := exists_F2_of_sep gates p hp hg hU hN S Q hw (canonPt Q) hZR
    (fun x hx => canonPt_eq_true.mpr hx) hu hu' huu (out w)
    (by rw [hev]; simpa using fun y hy => hZR y hy) (hone u hu) (hone u' hu')
  exact ⟨j, hj⟩

end F2Desc

section Merges

variable {n m : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

include hg hU in
/-- **Real merges are F2 gates**: a merge gate of the real run at a zero point `Z ⊇ Q` avoiding an
alive set is an OR gate (`mergeSet_or`) with the triple of its two merged points. -/
theorem mergeSet_subset_F2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) {w : Fin m}
    (hw : w ∈ aliveSets S Q) (Z : Fin n → Bool) (hZR : ∀ x ∈ S w, Z x = false)
    (hZQ : ∀ x ∈ Q, Z x = true) : mergeSet gates (S w) Z ⊆ F2 gates S Q := by
  classical
  intro i hi
  obtain ⟨j, -, rfl, -⟩ := (runMT_mem Z (upPt Z) (S w) gates gates.length i).mp hi
  obtain ⟨hjl, hor⟩ := mergeSet_or gates hg hU (S w) Z j hi
  obtain ⟨⟨u, hu, u', hu', h1, h2, hne⟩, -⟩ := run_recordT Z (upPt Z) (S w) gates gates.length j hi
  have huu : u ≠ u' := fun h => hne (h ▸ rfl)
  have h0 : val gates Z (n + j) = false := by
    have h := mergeSet_subset_DT gates (S w) Z hi
    simp only [DT, Finset.mem_filter] at h
    exact h.2.1
  exact mem_F2.mpr ⟨⟨j, rfl, gates[j], List.getElem?_eq_getElem hjl, hor⟩, w, hw,
    Z, u, u', hu, hu', huu, hZR, hZQ, h0, h1, h2⟩

include hg hU in
/-- **MergeSDR ⇒ MU over F2** (pairwise disjoint real merge sets lie in `F2(∅)`, each with at least
`d_w` gates). -/
theorem muF2_of_mergeSDR (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (H : MergeSDR S gates) : MUF2 S gates := by
  classical
  obtain ⟨z, hz, hdis⟩ := H
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => mergeSet gates (S w) (z w) := fun w _ w' _ hww => hdis w w' hww
  have hall : ∀ w, w ∈ aliveSets S ∅ := fun w => mem_aliveSets.mpr (Finset.disjoint_empty_right _)
  unfold MUF2
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (mergeSet gates (S w) (z w)).card := Finset.sum_le_sum fun w _ => by
        refine mergeSet_card_ge gates hg hU (S w) (z w) (out w) ?_ fun u hu => ?_
        · rw [hev]
          simpa using fun y hy => hz w y hy
        · rw [hev]
          exact decide_eq_true ⟨u, hu, by simp [upPt]⟩
    _ = (Finset.univ.biUnion fun w => mergeSet gates (S w) (z w)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (F2 gates S ∅).card := Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ =>
        mergeSet_subset_F2 gates hg hU S ∅ (hall w) (z w) (hz w) (by simp))

end Merges

section F1

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **F1** (front A2): `v` heavy over `Q` ⇒ a gate with a real witness above `Q ∪ {v}` is `0` at
`Q ∪ {v}`. -/
theorem F1_real_zero (R Q : Finset (Fin n)) (v : Fin n)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false) {i : ℕ}
    (hi : F2Wit gates R (insert v Q) i) : val gates (canonPt (insert v Q)) i = false := by
  obtain ⟨Z, -, -, -, -, -, -, hZQ, hz, -⟩ := hi
  have hle : canonPt (insert v Q) ≤ Z := canonPt_le fun c hc => hZQ c hc
  have hNZ := not_false_of_le gates p hp hg hU hN hle hv
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have e1 := val_lift (n := n) gates p hp (canonPt (insert v Q)) i
  have e2 := val_lift (n := n) gates p hp Z i
  rw [hv] at e1
  rw [hNZ] at e2
  have hmono := val_le_of_le (lift n p gates) hm.andOr (ext_le_of_le hle (le_refl false))
    (liftWire n p i)
  rw [← e1, ← e2, hz] at hmono
  exact le_bot_iff.mp hmono

include hg hU hN in
/-- **The F1 count**: for `v` heavy over `Q`, the `F2(Q)` gates that are `1` at `Q ∪ {v}` leave F2
under `x_v := 1`. -/
theorem card_real_le_gainF2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false) :
    ((F2 gates S Q).filter fun i => val gates (canonPt (insert v Q)) i = true).card ≤
      (F2 gates S Q \ F2 gates S (insert v Q)).card := by
  refine Finset.card_le_card fun i hi => ?_
  obtain ⟨hi, h1⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_sdiff.mpr ⟨hi, fun hi' => ?_⟩
  obtain ⟨-, w, -, hwit⟩ := mem_F2.mp hi'
  rw [F1_real_zero gates p hp hg hU hN (S w) Q v hv hwit] at h1
  exact absurd h1 (by decide)

end F1

end PEqualNP.Outside.L_meta_951_aux
