import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.GraphHeavy
import PEqualNP.W951.F2Induct
import PEqualNP.W951.F2Bridge

/-!
# GraphHeavyF2: front A2's G1 (graph systems, chosen heavy `v`) in F2-gain form

Coord 12:46: the induction counts F2 (real witnesses, `F2Induct.lean`). This file turns the G1 star
classes of `GraphHeavy.lean` (I0 classes at `top_va`, world 0) into REAL gates of
`F2(Q) \ F2(Q ∪ {v})`, through the bridge of `F2Bridge.lean`, under the extra hypothesis that every
star set's zero point is in world 0: `h(top_va) = 1` (the NOT gate is `0` at `Zof S_w`). This is front
A2's (F5): "the G1 gate `g_a` has the real witness `(top_va, v, a)` when `h(top_va) = 1`".

* `aAtom_of_mem_starCls`: a gate of a star class is `1` at the `a`-atom `(M_a ∪ {a}, 0)`.
* `lowerWire_mem_F2`: the real wire of a star-class gate lies in `F2(Q)` (witness `Z = top_va`,
  `u = v`, `u' = a`) and not in `F2(Q ∪ {v})` (Lemma C0 for F2).
* `gainF2_graphStar`: `gainOne_graphStar`'s hypotheses plus `h(top_va) = 1` for every star set ⇒
  `GainF2` at `v`. Stated for a CHOSEN `v` (front: "heavy `v` exists ⇒ works" is refuted for F2).
* `gainF2_G1`: G1's atoms (`g1M`) under the same extra hypothesis.

Open (front A2): star sets with `h(top_va) = 0` (the bridge from lifted to real witnesses there).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section GraphHeavyF2

variable {n m : ℕ}

theorem aAtom_of_mem_starCls (gates : List Gate) (p : ℕ) (R Q : Finset (Fin n)) (v : Fin n)
    (M : Fin n → Finset (Fin n)) (hR : R.card = 2) (hvR : v ∈ R) {a : Fin n} (haR : a ∈ R)
    (hav : a ≠ v) {i : ℕ} (hi : i ∈ pureCls gates p R (.zero (starM Q v M))) :
    val (lift n p gates) (ext (canonPt (insert a (M a))) false) i = true := by
  classical
  have h1 := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h1
  obtain ⟨-, -, c, c', hcc, hc, hc', h1c, h1c'⟩ := h1
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨u', hu', rfl⟩ := mem_liftSet_iff.mp hc'
  have hatom : atom0 (starM Q v M) (Fin.castSucc a) = ext (canonPt (insert a (M a))) false := by
    rw [atom0_castSucc, starM, ite_eq_right hav]
  rcases mem_pair_of_card_two hR hvR haR hav hu with rfl | rfl
  · rcases mem_pair_of_card_two hR hvR haR hav hu' with rfl | rfl
    · exact absurd rfl hcc
    · rwa [hatom] at h1c'
  · rwa [hatom] at h1c

theorem lowerWire_injOn {p i i' : ℕ} (hi : n + 1 ≤ i) (hi' : n + 1 ≤ i')
    (h : lowerWire n p i = lowerWire n p i') : i = i' := by
  have := realWire_injective n p h
  omega

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp in
/-- The real wire of a lifted OR gate is a real OR gate. -/
theorem lowerWire_isOr {j : ℕ} (hj : j < (lift n p gates).length) (hor : IsOrAt (lift n p gates) j) :
    ∃ k, lowerWire n p (n + 1 + j) = n + k ∧ IsOrAt gates k := by
  have hlen := length_lift n p gates hp
  set k := if j < p then j else j + 1 with hk
  have hkl : k < gates.length := by rw [hk]; split_ifs <;> omega
  have hkp : k ≠ p := by rw [hk]; split_ifs <;> omega
  have hidx : liftIdx p k = j := by rw [hk]; unfold liftIdx; split_ifs <;> omega
  refine ⟨k, ?_, (isOrAt_lift_iff n hp hkl hkp).mp (hidx ▸ hor)⟩
  unfold lowerWire realWire
  rw [hk]
  split_ifs <;> omega

include hg hU hN in
/-- **A star-class gate is a real F2 gate leaving under `x_v := 1`.** For a two-point star set
`S_w = {v, a}` alive at `Q`, valid atoms (`v ∉ M_a`) and `h(top_va) = 1`, the real wire of a gate of
the star class lies in `F2(Q) \ F2(Q ∪ {v})`. -/
theorem lowerWire_mem_F2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (M : Fin n → Finset (Fin n)) {w : Fin m} (hw : w ∈ starSets S Q v) (h2 : (S w).card = 2)
    {a : Fin n} (haw : a ∈ S w) (hav : a ≠ v) (hvM : v ∉ M a)
    (htop : val gates (Zof (S w)) (n + p) = false)
    (hvalid : PureValid gates p (S w) (.zero (starM Q v M))) {i : ℕ}
    (hi : i ∈ pureCls gates p (S w) (.zero (starM Q v M))) :
    lowerWire n p i ∈ F2 gates S Q \ F2 gates S (insert v Q) := by
  classical
  have hstar := Finset.mem_filter.mp hw
  obtain ⟨hwa, hvw⟩ := hstar
  have hQw := mem_aliveSets.mp hwa
  have hQ0 : ∀ x ∈ Q, (PureOpt.zero (starM Q v M)).zeroPt (S w) x = true := by
    intro x hx
    have : x ∉ S w := fun h => Finset.disjoint_left.mp hQw h hx
    simp [PureOpt.zeroPt, Zof, this]
  obtain ⟨⟨j, rfl, hor⟩, -⟩ := pureCls_UCWit gates p hp hg hU hN (S w) Q _ hvalid hQ0 hi
  have hjl : j < (lift n p gates).length := by
    obtain ⟨g, hg', -⟩ := hor
    exact (List.getElem?_eq_some_iff.mp hg').1
  have hge : n + 1 ≤ n + 1 + j := by omega
  have hC0 := C0_of_mem_starCls gates p (S w) Q v M h2 hvw hi
  refine Finset.mem_sdiff.mpr ⟨?_, fun hi' => ?_⟩
  · obtain ⟨k, hk, hork⟩ := lowerWire_isOr gates p hp hjl hor
    refine mem_F2.mpr ⟨⟨k, hk, hork⟩, w, hwa, Zof (S w), v, a, hvw, haw, Ne.symm hav,
      fun x hx => by simp [Zof, hx], fun x hx => ?_, ?_, ?_, ?_⟩
    · have : x ∉ S w := fun h => Finset.disjoint_left.mp hQw h hx
      simp [Zof, this]
    · -- `0` at `top_va` (world 0 there)
      refine real_zero_of_lift gates p hp hg hU hN hge (ζ := ext (Zof (S w)) false) ?_ ?_
      · rw [nuPt, htop]
      · exact pureI0At_zero (show n + 1 + j ∈ pureI0At gates p (S w) (Zof (S w)) (starM Q v M) from hi)
    · -- `1` at `top_va + e_v`
      refine real_one_of_lift gates p hp hg hU hN hge (ext_le_of_le (canonPt_le fun x hx => ?_)
        (Bool.false_le _)) hC0
      by_cases hxv : x = v
      · subst hxv; simp
      · rw [Function.update_of_ne hxv]
        have hxQ : x ∈ Q := (Finset.mem_insert.mp hx).resolve_left hxv
        have : x ∉ S w := fun h => Finset.disjoint_left.mp hQw h hxQ
        simp [Zof, this]
    · -- `1` at `top_va + e_a`
      refine real_one_of_lift gates p hp hg hU hN hge (ext_le_of_le (canonPt_le fun x hx => ?_)
        (Bool.false_le _)) (aAtom_of_mem_starCls gates p (S w) Q v M h2 hvw haw hav hi)
      by_cases hxa : x = a
      · subst hxa; simp
      · rw [Function.update_of_ne hxa]
        have hxM : x ∈ M a := (Finset.mem_insert.mp hx).resolve_left hxa
        have hxv : x ≠ v := fun h => hvM (h ▸ hxM)
        have : x ∉ S w := fun h => by
          rcases mem_pair_of_card_two h2 hvw haw hav h with h | h
          · exact hxv h
          · exact hxa h
        simp [Zof, this]
  · obtain ⟨-, w', -, hwit⟩ := mem_F2.mp hi'
    refine not_F2Wit_of_C0 gates p hp hg hU hN (S w') (insert v Q) ?_ hwit
    rw [liftWire_lowerWire p _ hge]
    exact hC0

include hg hU hN in
/-- **The graph star gain in F2** (G1's general form). `gainOne_graphStar`'s hypotheses plus
`h(top_va) = 1` for every star set ⇒ `GainF2` at `v`. -/
theorem gainF2_graphStar (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n) (M : Fin n → Finset (Fin n))
    (h2 : ∀ w ∈ starSets S Q v, (S w).card = 2)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hM : ∀ w ∈ starSets S Q v, ∀ a ∈ S w, a ≠ v →
      v ∉ M a ∧ val gates (canonPt (M a)) (n + p) = false)
    (hsep : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → ∀ a ∈ S w, a ≠ v →
      ∀ b ∈ S w', b ≠ v → b ∉ M a ∨ a ∉ M b)
    (htop : ∀ w ∈ starSets S Q v, val gates (Zof (S w)) (n + p) = false) :
    GainF2 gates S Q v := by
  classical
  set mm := starM Q v M with hmm
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  have hvalid : ∀ w ∈ starSets S Q v, PureValid gates p (S w) (.zero mm) := by
    intro w hw
    obtain ⟨hwa, hvw⟩ := (hstar w).mp hw
    have hQ := mem_aliveSets.mp hwa
    refine ⟨fun u hu x hx hxR => ?_, fun u hu => ?_⟩
    · by_cases huv : u = v
      · subst huv
        rw [hmm, starM, ite_eq_left rfl] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rfl
        · exact absurd hx (Finset.disjoint_left.mp hQ hxR)
      · rw [hmm, starM, ite_eq_right huv] at hx
        rcases mem_pair_of_card_two (h2 w hw) hvw hu huv hxR with rfl | rfl
        · exact absurd hx (hM w hw u hu huv).1
        · rfl
    · by_cases huv : u = v
      · subst huv
        rw [hmm, starM, ite_eq_left rfl]
        exact hQv
      · rw [hmm, starM, ite_eq_right huv]
        exact (hM w hw u hu huv).2
  -- the real classes
  have hsub : ∀ w ∈ starSets S Q v, (pureCls gates p (S w) (.zero mm)).image (lowerWire n p) ⊆
      F2 gates S Q \ F2 gates S (insert v Q) := by
    intro w hw x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨-, hvw⟩ := (hstar w).mp hw
    obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne (by rw [h2 w hw]; norm_num) v
    exact lowerWire_mem_F2 gates p hp hg hU hN S Q v M hw (h2 w hw) ha hav (hM w hw a ha hav).1
      (htop w hw) (hvalid w hw) hi
  have hge : ∀ w, ∀ i ∈ pureCls gates p (S w) (.zero mm), n + 1 ≤ i := fun w i hi =>
    (Finset.mem_Ico.mp (pureCls_subset gates p (S w) _ hi)).1
  -- the lifted classes are pairwise disjoint (as in `gainOne_graphStar`)
  have hdisL : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
      Disjoint (pureCls gates p (S w) (.zero mm)) (pureCls gates p (S w') (.zero mm)) := by
    intro w hw w' hw' hww
    obtain ⟨-, hvw⟩ := (hstar w).mp hw
    obtain ⟨-, hvw'⟩ := (hstar w').mp hw'
    obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne (by rw [h2 w hw]; norm_num) v
    obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_ne (by rw [h2 w' hw']; norm_num) v
    have hab : a ≠ b := by
      rintro rfl
      have hsub2 : ({v, a} : Finset (Fin n)) ⊆ S w ∩ S w' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_inter.mpr ⟨hvw, hvw'⟩
        · rw [Finset.mem_singleton.mp hy]
          exact Finset.mem_inter.mpr ⟨ha, hb⟩
      have := Finset.card_le_card hsub2
      rw [Finset.card_pair (Ne.symm hav)] at this
      have := hinter w hw w' hw' hww
      omega
    rcases hsep w hw w' hw' hww a ha hav b hb hbv with h | h
    · exact disjoint_starCls gates p hp hg hU hN Q v M (S w) (S w') (h2 w hw) (h2 w' hw') hvw hvw'
        ha hav hb hbv hab (hM w hw a ha hav).1 h
    · exact (disjoint_starCls gates p hp hg hU hN Q v M (S w') (S w) (h2 w' hw') (h2 w hw) hvw' hvw
        hb hbv ha hav (Ne.symm hab) (hM w' hw' b hb hbv).1 h).symm
  have hpd : ((starSets S Q v : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => (pureCls gates p (S w) (.zero mm)).image (lowerWire n p) := by
    intro w hw w' hw' hww
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i', hi', hii⟩ := Finset.mem_image.mp hx'
    have := lowerWire_injOn (hge w' i' hi') (hge w i hi) hii
    subst this
    exact Finset.disjoint_left.mp (hdisL w hw w' hw' hww) hi hi'
  unfold GainF2
  calc ∑ w ∈ starSets S Q v, ((S w).card - 1)
      ≤ ∑ w ∈ starSets S Q v, ((pureCls gates p (S w) (.zero mm)).image (lowerWire n p)).card :=
        Finset.sum_le_sum fun w hw => by
          rw [Finset.card_image_of_injOn fun i hi i' hi' h => lowerWire_injOn (hge w i hi) (hge w i' hi') h]
          exact card_pureCls gates p hp hg hU hN (S w) _ (hvalid w hw) (out w) (hev w)
    _ = ((starSets S Q v).biUnion fun w => (pureCls gates p (S w) (.zero mm)).image (lowerWire n p)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (F2 gates S Q \ F2 gates S (insert v Q)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

include hg hU hN in
/-- **G1 in F2-gain form** (front A2's (F5)): G1's hypotheses plus `h(top_va) = 1` for every star set
⇒ `GainF2` at `v`. -/
theorem gainF2_G1 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (h2 : ∀ w ∈ starSets S Q v, (S w).card = 2)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hX : ∀ a ∈ lightNbr gates p S Q v,
      val gates (canonPt (insert a (g1X gates p S Q v))) (n + p) = false)
    (htop : ∀ w ∈ starSets S Q v, val gates (Zof (S w)) (n + p) = false) :
    GainF2 gates S Q v := by
  classical
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  have hnotQ : ∀ w ∈ starSets S Q v, ∀ x ∈ S w, x ∉ Q := fun w hw x hx hxQ =>
    Finset.disjoint_left.mp (mem_aliveSets.mp ((hstar w).mp hw).1) hx hxQ
  have hvX : v ∉ g1X gates p S Q v := by simp [g1X]
  have hLX : ∀ b ∈ lightNbr gates p S Q v, b ∉ g1X gates p S Q v := by
    intro b hb
    simp [g1X, hb]
  refine gainF2_graphStar gates p hp hg hU hN S out hev Q v (g1M gates p S Q v) h2 hinter hQv
    (fun w hw a ha hav => ?_) (fun w hw w' hw' hww a ha hav b hb hbv => ?_) htop
  · by_cases hL : a ∈ lightNbr gates p S Q v
    · rw [g1M, ite_eq_left hL]
      refine ⟨fun h => ?_, hX a hL⟩
      rcases Finset.mem_insert.mp h with h | h
      · exact hav h.symm
      · exact hvX h
    · rw [g1M, ite_eq_right hL]
      refine ⟨fun h => ?_, ?_⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact hav h.symm
        · exact hnotQ w hw v ((hstar w).mp hw).2 h
      · cases hval : val gates (canonPt (insert a Q)) (n + p)
        · rfl
        · exact absurd ((mem_lightNbr gates p).mpr ⟨hav, ⟨w, hw, ha⟩, hval⟩) hL
  · have hab : a ≠ b := by
      rintro rfl
      have hsub2 : ({v, a} : Finset (Fin n)) ⊆ S w ∩ S w' := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_inter.mpr ⟨((hstar w).mp hw).2, ((hstar w').mp hw').2⟩
        · rw [Finset.mem_singleton.mp hy]
          exact Finset.mem_inter.mpr ⟨ha, hb⟩
      have := Finset.card_le_card hsub2
      rw [Finset.card_pair (Ne.symm hav)] at this
      have := hinter w hw w' hw' hww
      omega
    by_cases hLa : a ∈ lightNbr gates p S Q v
    · by_cases hLb : b ∈ lightNbr gates p S Q v
      · left
        rw [g1M, ite_eq_left hLa]
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hab h.symm
        · exact hLX b hLb h
      · right
        rw [g1M, ite_eq_right hLb]
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hab h
        · exact hnotQ w hw a ha h
    · left
      rw [g1M, ite_eq_right hLa]
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hab h.symm
      · exact hnotQ w' hw' b hb h

end GraphHeavyF2

end PEqualNP.Outside.L_meta_951_aux
