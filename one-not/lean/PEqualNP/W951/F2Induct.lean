import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MUInduct

/-!
# F2Induct: the point induction over F2 (real witnesses)

Coord's DECISION 12:46: the point induction counts **F2**, the OR gates of the REAL circuit with a
real witness: a set `w` alive at `Q`, a point `Z ⊇ Q` avoiding `S_w`, two points `u ≠ u'` of `S_w` with
`g(Z) = 0` and `g(Z + e_u) = g(Z + e_u') = 1`. No lift, no NOT gate and no world in the definition.

* `F2Wit`, `F2 gates S Q` (real wire numbers), `mem_F2`, `F2_mono` / `F2_insert_subset` (heredity
  under `x_v := 1`), `F2_subset` (the gate wires), `card_F2_le` (`|F2| ≤ s`).
* `GainF2` (`∑_{alive w ∋ v} d_w ≤ |F2(Q) \ F2(Q ∪ {v})|`), `base_le_F2_pts` (a gain at some `v ∉ Q`
  for every `Q` with positive base ⇒ `base(Q) ≤ |F2(Q)|`), `MUF2`, **`no_minCE_of_MUF2`** (`base ≤ |F2|
  ≤ s` contradicts `s < base`; no NOT gate used), **`no_minCE_of_gainF2`**.
* The link to the lift (one NOT gate at `p`): `F2Wit.ucWit` (a real witness is a UC witness of the
  lifted wire: world 1 if the NOT gate is `1` at `Z`, world 0 otherwise), `card_F2_le_UC`
  (`|F2(Q)| ≤ |UC(∅, Q)|`, so MUF2 ⇒ MUC), and Lemma C0 for F2 (`not_F2Wit_of_C0`: `C_0(g)(Q) = 1` ⇒
  `g` has no real witness above `Q`; `card_C0_le_gainF2`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section F2Induct

variable {n m : ℕ}

/-- **The real witness** of wire `i` for the set `R` with `Q` fixed to `1`. -/
def F2Wit (gates : List Gate) (R Q : Finset (Fin n)) (i : ℕ) : Prop :=
  ∃ (Z : Fin n → Bool) (u u' : Fin n), u ∈ R ∧ u' ∈ R ∧ u ≠ u' ∧ (∀ x ∈ R, Z x = false) ∧
    (∀ x ∈ Q, Z x = true) ∧ val gates Z i = false ∧ val gates (Function.update Z u true) i = true ∧
    val gates (Function.update Z u' true) i = true

theorem F2Wit.mono {gates : List Gate} {R Q Q' : Finset (Fin n)} {i : ℕ} (hQ : Q ⊆ Q')
    (h : F2Wit gates R Q' i) : F2Wit gates R Q i := by
  obtain ⟨Z, u, u', hu, hu', huu, hZR, hZQ, rest⟩ := h
  exact ⟨Z, u, u', hu, hu', huu, hZR, fun x hx => hZQ x (hQ hx), rest⟩

open Classical in
/-- **F2**: the OR gates of the real circuit with a real witness for a set alive at `Q`. -/
noncomputable def F2 (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter fun i =>
    IsOrAt gates (i - n) ∧ ∃ w ∈ aliveSets S Q, F2Wit gates (S w) Q i

theorem mem_F2 {gates : List Gate} {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)} {i : ℕ} :
    i ∈ F2 gates S Q ↔ (∃ k, i = n + k ∧ IsOrAt gates k) ∧
      ∃ w ∈ aliveSets S Q, F2Wit gates (S w) Q i := by
  classical
  rw [F2, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, -⟩, hor, hw⟩
    exact ⟨⟨i - n, by omega, hor⟩, hw⟩
  · rintro ⟨⟨k, rfl, hor⟩, hw⟩
    obtain ⟨g, hg, hgo⟩ := hor
    have hk : k < gates.length := (List.getElem?_eq_some_iff.mp hg).1
    refine ⟨⟨by omega, by omega⟩, ?_, hw⟩
    rw [Nat.add_sub_cancel_left]
    exact ⟨g, hg, hgo⟩

/-- **Heredity**: more points fixed to `1` give a smaller F2. -/
theorem F2_mono (gates : List Gate) (S : Fin m → Finset (Fin n)) {Q Q' : Finset (Fin n)}
    (hQ : Q ⊆ Q') : F2 gates S Q' ⊆ F2 gates S Q := by
  intro i hi
  obtain ⟨hor, w, hw, hwit⟩ := mem_F2.mp hi
  exact mem_F2.mpr ⟨hor, w, mem_aliveSets.mpr (Finset.disjoint_of_subset_right hQ
    (mem_aliveSets.mp hw)), hwit.mono hQ⟩

/-- `x_v := 1`: `F2(Q ∪ {v}) ⊆ F2(Q)`. -/
theorem F2_insert_subset (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n))
    (v : Fin n) : F2 gates S (insert v Q) ⊆ F2 gates S Q :=
  F2_mono gates S (Finset.subset_insert v Q)

theorem F2_subset (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    F2 gates S Q ⊆ Finset.Ico n (n + gates.length) := by
  classical
  exact Finset.filter_subset _ _

/-- `|F2| ≤ s`. -/
theorem card_F2_le (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    (F2 gates S Q).card ≤ gates.length := by
  have h := Finset.card_le_card (F2_subset gates S Q)
  rw [Nat.card_Ico] at h
  omega

/-! ## The induction -/

/-- **The F2 step at `v`** (`x_v := 1`): `∑_{alive w ∋ v} d_w ≤ |F2(Q) \ F2(Q ∪ {v})|`. -/
def GainF2 (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ (F2 gates S Q \ F2 gates S (insert v Q)).card

/-- **The F2 induction on the unfixed points**: at every `Q` with positive base, some `v ∉ Q` has the
F2 step ⇒ `base(Q) ≤ |F2(Q)|`. -/
theorem base_le_F2_pts (gates : List Gate) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainF2 gates S Q v) :
    ∀ k (Q : Finset (Fin n)), (Finset.univ \ Q).card ≤ k →
      baseDQ S ∅ Q ≤ (F2 gates S Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvQ, -⟩ := H Q hpos
    have : v ∈ Finset.univ \ Q := by simp [hvQ]
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hk)] at this
    exact absurd this (Finset.notMem_empty v)
  | succ k ih =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨v, hvQ, hgain⟩ := H Q hpos
    have hv : v ∈ Finset.univ \ Q := by simp [hvQ]
    have hih := ih (insert v Q) (by rw [Finset.sdiff_insert, Finset.card_erase_of_mem hv]; omega)
    have hb := baseDQ_insertQ S ∅ Q v
    have hcard := Finset.card_sdiff_add_card_eq_card (F2_insert_subset gates S Q v)
    have hstar : ∑ w ∈ starSets S Q v, ((S w \ ∅).card - 1) =
        ∑ w ∈ starSets S Q v, ((S w).card - 1) := by simp
    unfold GainF2 at hgain
    omega

/-- **MU over F2**: `base ≤ |F2(∅)|`. -/
def MUF2 (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∑ w, ((S w).card - 1) ≤ (F2 gates S ∅).card

theorem muF2_of_gainF2 (gates : List Gate) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainF2 gates S Q v) : MUF2 S gates := by
  have h := base_le_F2_pts gates S H _ ∅ le_rfl
  rwa [baseDQ_empty] at h

/-! ## The link to the lift: F2 ⊆ UC, Lemma C0 for F2 -/

section Lift

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **A real witness is a UC witness** of the lifted wire (world 1 if the NOT gate is `1` at `Z`,
world 0 otherwise: the real circuit lies between `C_0` and `C_1`, and the NOT gate is antitone). -/
theorem F2Wit.ucWit {R Q : Finset (Fin n)} {i : ℕ} (h : F2Wit gates R Q i) :
    UCWit gates p R ∅ Q (liftWire n p i) := by
  obtain ⟨Z, u, u', hu, hu', huu, hZR, hZQ, hz, h1, h2⟩ := h
  have hl := fun x => val_lift (n := n) gates p hp x i
  cases hZ : val gates Z (n + p) with
  | true =>
    refine ⟨true, Z, u, u', hu, hu', huu, by simp, by simp, hZR, by simp, hZQ, hZ, ?_, ?_, ?_⟩
    · have e := hl Z
      rw [hZ] at e
      rw [← e]
      exact hz
    · exact (lift_exact (n := n) gates p hp hg hU hN _ i).2.1 h1
    · exact (lift_exact (n := n) gates p hp hg hU hN _ i).2.1 h2
  | false =>
    have hle : ∀ y, Z ≤ Function.update Z y true := by
      intro y c
      by_cases hc : c = y
      · subst hc
        simp
      · rw [Function.update_of_ne hc]
    have hN1 := not_false_of_le gates p hp hg hU hN (hle u) hZ
    have hN2 := not_false_of_le gates p hp hg hU hN (hle u') hZ
    refine ⟨false, Z, u, u', hu, hu', huu, by simp, by simp, hZR, by simp, hZQ, ⟨hN1, hN2⟩, ?_, ?_,
      ?_⟩
    · have e := hl Z
      rw [hZ] at e
      rw [← e]
      exact hz
    · have e := hl (Function.update Z u true)
      rw [hN1] at e
      rw [← e]
      exact h1
    · have e := hl (Function.update Z u' true)
      rw [hN2] at e
      rw [← e]
      exact h2

theorem liftWire_injOn (i i' : ℕ) (hi : n ≤ i) (hi' : n ≤ i') (hip : i ≠ n + p) (hip' : i' ≠ n + p)
    (h : liftWire n p i = liftWire n p i') : i = i' := by
  unfold liftWire at h
  split_ifs at h <;> omega

include hg hU hN in
/-- **F2 ⊆ UC** (through the lifted wire numbers): `|F2(Q)| ≤ |UC(∅, Q)|`. -/
theorem card_F2_le_UC (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    (F2 gates S Q).card ≤ (UC gates p S ∅ Q).card := by
  classical
  have hmap : ∀ i ∈ F2 gates S Q, liftWire n p i ∈ UC gates p S ∅ Q ∧ n ≤ i ∧ i ≠ n + p := by
    intro i hi
    obtain ⟨⟨k, rfl, hor⟩, w, hw, hwit⟩ := mem_F2.mp hi
    obtain ⟨g, hgk, hgo⟩ := hor
    have hk : k < gates.length := (List.getElem?_eq_some_iff.mp hgk).1
    have hkp : k ≠ p := by
      rintro rfl
      have : gates[k] = g := (List.getElem?_eq_some_iff.mp hgk).2
      rw [this, hgo] at hN
      exact GateOp.noConfusion hN
    refine ⟨mem_UC.mpr ⟨⟨liftIdx p k, liftWire_gate n p k hkp,
      (isOrAt_lift_iff n hp hk hkp).mpr ⟨g, hgk, hgo⟩⟩, w, hw,
      hwit.ucWit gates p hp hg hU hN⟩, by omega, by omega⟩
  calc (F2 gates S Q).card = ((F2 gates S Q).image (liftWire n p)).card :=
        (Finset.card_image_of_injOn fun i hi i' hi' h =>
          liftWire_injOn p i i' (hmap i hi).2.1 (hmap i' hi').2.1 (hmap i hi).2.2 (hmap i' hi').2.2 h).symm
    _ ≤ (UC gates p S ∅ Q).card := Finset.card_le_card fun j hj => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact (hmap i hi).1

include hg hU hN in
/-- **MUF2 ⇒ MUC.** -/
theorem muc_of_muF2 (S : Fin m → Finset (Fin n)) (H : MUF2 S gates) : MUC S gates p :=
  H.trans (card_F2_le_UC gates p hp hg hU hN S ∅)

include hg hU hN in
/-- **Lemma C0 for F2**: if `C_0(g)` is `1` at `Q` (lifted wire), the real gate `g` has no real witness
with `Q` fixed to `1` (`C_0` is monotone and the real circuit lies above it). -/
theorem not_F2Wit_of_C0 (R Q : Finset (Fin n)) {i : ℕ}
    (h0 : val (lift n p gates) (ext (canonPt Q) false) (liftWire n p i) = true) :
    ¬ F2Wit gates R Q i := by
  rintro ⟨Z, -, -, -, -, -, -, hZQ, hz, -⟩
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hle := val_le_of_le (lift n p gates) hm.andOr
    (ext_le_of_le (canonPt_le fun c hc => hZQ c hc) (le_refl false)) (liftWire n p i)
  rw [h0] at hle
  have := (lift_exact (n := n) gates p hp hg hU hN Z i).1 (top_le_iff.mp hle)
  rw [hz] at this
  exact absurd this (by decide)

include hg hU hN in
/-- **The C0 count for F2**: the F2 gates whose `C_0` is `1` at `Q ∪ {v}` leave F2 under `x_v := 1`. -/
theorem card_C0_le_gainF2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    ((F2 gates S Q).filter fun i =>
        val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true).card ≤
      (F2 gates S Q \ F2 gates S (insert v Q)).card := by
  refine Finset.card_le_card fun i hi => ?_
  obtain ⟨hi, h0⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_sdiff.mpr ⟨hi, fun hi' => ?_⟩
  obtain ⟨-, w, -, hwit⟩ := mem_F2.mp hi'
  exact not_F2Wit_of_C0 gates p hp hg hU hN (S w) (insert v Q) h0 hwit

end Lift

end F2Induct

/-- **951 from MU over F2**: if every minimal counterexample has `base ≤ |F2(∅)|`, there is none
(`|F2| ≤ s < base`). No NOT gate and no lift. -/
theorem no_minCE_of_MUF2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → MUF2 S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  have h1 := H n m S gates out M
  have h2 := card_F2_le gates S ∅
  have h3 := M.ce.hlt
  unfold MUF2 at h1
  omega

/-- **951 from the F2 step** (coord's DECISION 12:46): if in every minimal counterexample every `Q`
with positive base has a point `v ∉ Q` with `|F2(Q) \ F2(Q ∪ {v})| ≥ ∑_{alive w ∋ v} d_w`, there is
no minimal counterexample. -/
theorem no_minCE_of_gainF2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ GainF2 gates S Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MUF2 fun n m S gates out M => muF2_of_gainF2 gates S (H n m S gates out M)

end PEqualNP.Outside.L_meta_951_aux
