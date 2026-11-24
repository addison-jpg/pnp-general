import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2Light

/-!
# F2FirstJoin: first-joining gates (dwV8p, `PROOF_PLAN_SUGGESTIONS.md` §6 Step 2', PROVED there)

`P` = the points of the star sets of `v` at `Q` (`starPts`), zero point `Q`, the real block of a wire
`i`: the points `x ∈ P` with `i` true at `Q + e_x`. For `u ∈ P \ {v}`, `firstJoin gates Q v u` is the
first wire that is `0` at `Q` and true at `Q + e_v` and `Q + e_u` (`JoinsAt`).

* `exists_joinsAt`: it exists (the output of a star set through `u` and `v`).
* `firstJoin_isOr`: it is an OR gate (an input joins at most one point; the NOT gate, if `0` at `Q`,
  is `0` above `Q`; an AND gate that joins has an earlier joining input).
* `firstJoin_mem_F2`, `firstJoin_mem_SEE`: `f(u) ∈ F2(Q) ∩ SEE(v)` (witness `Z = Q` with the star set
  through `u` and `v`).
* `firstJoinSet` (`F(v)`), `firstJoinSet_subset_SEE`, `card_firstJoinSet_le` (`|F(v)| ≤ cost(v)`; the difference is `deficit(v)`).
* `gainF2_of_firstJoin`: `f` injective on `P \ {v}` (deficit `0`) and no `f`-gate in `SURV(v)` ⇒ the F2 step
  (the immediate case: 19,613 / 19,620 random instances). For heavy `v` `SURV = ∅` (`gainF2_of_firstJoin_heavy`).
* `Absorb` (OPEN, dwV8p's ABSORB: `deficit(v) + |F(v) ∩ SURV(v)| ≤ |gain(v) \ F(v)|`) ⇒ the F2 step
  (`gainF2_of_absorb`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section FirstJoin

variable {n m : ℕ} (gates : List Gate)

theorem upPt_canonPt (Q : Finset (Fin n)) (v : Fin n) :
    upPt (canonPt Q) v = canonPt (insert v Q) := by
  funext c
  by_cases hc : c = v
  · subst hc
    simp [upPt, canonPt]
  · rw [upPt, Function.update_of_ne hc]
    simp [canonPt, hc]

/-- Wire `i` is `0` at `Q` and `1` at `Q + e_v` and `Q + e_u` (its block contains `v` and `u`). -/
def JoinsAt (Q : Finset (Fin n)) (v u : Fin n) (i : ℕ) : Prop :=
  val gates (canonPt Q) i = false ∧ val gates (upPt (canonPt Q) v) i = true ∧
    val gates (upPt (canonPt Q) u) i = true

open Classical in
/-- **The first-joining gate** `f(u)`: the first wire joining `v` and `u` at `Q`. -/
noncomputable def firstJoin (Q : Finset (Fin n)) (v u : Fin n) : ℕ :=
  if h : ∃ i, JoinsAt gates Q v u i then Nat.find h else 0

theorem firstJoin_spec {Q : Finset (Fin n)} {v u : Fin n} (h : ∃ i, JoinsAt gates Q v u i) :
    JoinsAt gates Q v u (firstJoin gates Q v u) ∧
      ∀ j < firstJoin gates Q v u, ¬ JoinsAt gates Q v u j := by
  classical
  rw [firstJoin, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- **Existence**: the output of a star set through `u` and `v` joins them. -/
theorem exists_joinsAt (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ starPts S Q v) :
    ∃ i, JoinsAt gates Q v u i := by
  obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨hwa, hvw⟩ := Finset.mem_filter.mp hw
  refine ⟨out w, ?_, ?_, ?_⟩
  · rw [hev]
    simpa using fun y hy => canonPt_zero_of_alive hwa y hy
  · rw [hev]
    exact decide_eq_true ⟨v, hvw, by simp [upPt]⟩
  · rw [hev]
    exact decide_eq_true ⟨u, huw, by simp [upPt]⟩

/-- `F(v)`: the first-joining gates of the points of `P \ {v}`. -/
noncomputable def firstJoinSet (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Finset ℕ :=
  ((starPts S Q v).erase v).image (firstJoin gates Q v)

variable (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **The first joining wire is an OR gate.** -/
theorem firstJoin_isOr (Q : Finset (Fin n)) {v u : Fin n} (huv : u ≠ v)
    (h : ∃ i, JoinsAt gates Q v u i) :
    ∃ k, firstJoin gates Q v u = n + k ∧ IsOrAt gates k := by
  obtain ⟨⟨h0, h1, h2⟩, hmin⟩ := firstJoin_spec gates h
  set i := firstJoin gates Q v u
  set Z := canonPt Q
  by_cases hin : i < n
  · rw [val_input gates Z i hin] at h0
    rw [val_input gates _ i hin] at h1 h2
    have e1 : (⟨i, hin⟩ : Fin n) = v := by
      by_contra hc
      rw [upPt, Function.update_of_ne hc, h0] at h1
      exact absurd h1 (by decide)
    have e2 : (⟨i, hin⟩ : Fin n) = u := by
      by_contra hc
      rw [upPt, Function.update_of_ne hc, h0] at h2
      exact absurd h2 (by decide)
    exact absurd (e2.symm.trans e1) huv
  by_cases hil : n + gates.length ≤ i
  · rw [mr_val_ge gates _ i hil] at h1
    exact absurd h1 (by decide)
  obtain ⟨k, hik⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
  have hk : k < gates.length := by omega
  rw [hik] at h0 h1 h2
  refine ⟨k, hik, ?_⟩
  rcases (hg _ (List.getElem_mem hk)).1 with hop | hop | hop
  · exfalso
    rw [mr_val_gate gates Z k hk, hop] at h0
    rw [mr_val_gate gates _ k hk, hop] at h1 h2
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id] at h0 h1 h2
    obtain ⟨a, ha, haz⟩ := h0
    have hva := h1 a ha
    have hua := h2 a ha
    have ha' : a < n + k := by
      by_contra hc
      rw [mr_val_ge (gates.take k) _ a (by simp; omega)] at hva
      exact absurd hva (by simp)
    rw [← mr_val_take gates _ k a ha'] at hva hua
    have haz' : val gates Z a = false := by
      rw [mr_val_take gates _ k a ha']
      simpa using haz
    exact hmin a (by omega) ⟨haz', hva, hua⟩
  · exact ⟨gates[k], List.getElem?_eq_getElem hk, hop⟩
  · exfalso
    have hkp : k = p := hU k p hk hp hop hN
    rw [hkp] at h0 h1
    have := not_false_of_le gates p hp hg hU hN (le_upPt Z v) h0
    rw [this] at h1
    exact absurd h1 (by decide)

include hg hU hN in
/-- **`f(u) ∈ F2(Q)`** (witness `Z = Q` with the star set through `u` and `v`). -/
theorem firstJoin_mem_F2 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ (starPts S Q v).erase v) :
    firstJoin gates Q v u ∈ F2 gates S Q := by
  obtain ⟨huv, huP⟩ := Finset.mem_erase.mp hu
  have hex := exists_joinsAt gates S out hev Q v huP
  obtain ⟨⟨h0, h1, h2⟩, -⟩ := firstJoin_spec gates hex
  obtain ⟨k, hk, hor⟩ := firstJoin_isOr gates p hp hg hU hN Q huv hex
  obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp huP
  obtain ⟨hwa, hvw⟩ := Finset.mem_filter.mp hw
  refine mem_F2.mpr ⟨⟨k, hk, hor⟩, w, hwa, canonPt Q, v, u, hvw, huw, Ne.symm huv,
    canonPt_zero_of_alive hwa, fun x hx => canonPt_eq_true.mpr hx, h0, h1, h2⟩

include hg hU hN in
/-- **`f(u) ∈ SEE(v)`**. -/
theorem firstJoin_mem_SEE (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) {u : Fin n} (hu : u ∈ (starPts S Q v).erase v) :
    firstJoin gates Q v u ∈ SEE gates S Q v := by
  classical
  have hex := exists_joinsAt gates S out hev Q v (Finset.mem_erase.mp hu).2
  obtain ⟨⟨-, h1, -⟩, -⟩ := firstJoin_spec gates hex
  refine Finset.mem_filter.mpr ⟨firstJoin_mem_F2 gates p hp hg hU hN S out hev Q v hu, ?_⟩
  rwa [← upPt_canonPt]

include hg hU hN in
theorem firstJoinSet_subset_SEE (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n) : firstJoinSet gates S Q v ⊆ SEE gates S Q v := by
  intro i hi
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
  exact firstJoin_mem_SEE gates p hp hg hU hN S out hev Q v hu

/-- `|F(v)| ≤ cost(v)` (the star sets meeting pairwise in at most one point); the difference is the
deficit. -/
theorem card_firstJoinSet_le (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1) :
    (firstJoinSet gates S Q v).card ≤ ∑ w ∈ starSets S Q v, ((S w).card - 1) := by
  classical
  rcases (starSets S Q v).eq_empty_or_nonempty with h0 | hne
  · have : starPts S Q v = ∅ := by simp [starPts, h0]
    simp [firstJoinSet, this]
  have hc := card_starPts S Q v hne hinter
  have hvP : v ∈ starPts S Q v := by
    obtain ⟨w, hw⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Finset.mem_filter.mp hw).2⟩
  have h1 := Finset.card_image_le (s := (starPts S Q v).erase v) (f := firstJoin gates Q v)
  rw [Finset.card_erase_of_mem hvP] at h1
  unfold firstJoinSet
  omega

include hg hU hN in
/-- **The immediate case**: `f` injective on `P \ {v}` (deficit `0`) and no `f`-gate survives ⇒ the F2
step. -/
theorem gainF2_of_firstJoin (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hinj : Set.InjOn (firstJoin gates Q v) ((starPts S Q v).erase v : Set (Fin n)))
    (hsurv : Disjoint (firstJoinSet gates S Q v) (SURV gates S Q v)) : GainF2 gates S Q v := by
  classical
  rcases (starSets S Q v).eq_empty_or_nonempty with h0 | hne
  · unfold GainF2
    rw [h0, Finset.sum_empty]
    exact Nat.zero_le _
  have hc := card_starPts S Q v hne hinter
  have hvP : v ∈ starPts S Q v := by
    obtain ⟨w, hw⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, (Finset.mem_filter.mp hw).2⟩
  have hcard : (firstJoinSet gates S Q v).card = ∑ w ∈ starSets S Q v, ((S w).card - 1) := by
    rw [firstJoinSet, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hvP]
    omega
  have hsub : firstJoinSet gates S Q v ⊆ (SEE gates S Q v \ SURV gates S Q v) ∪ K3 gates S Q v := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨firstJoinSet_subset_SEE gates p hp hg hU hN S out hev Q v hi, Finset.disjoint_left.mp hsurv hi⟩)
  exact gainF2_of_seeK3 gates S Q v (hcard.symm.le.trans (Finset.card_le_card hsub))

include hg hU hN in
/-- **The immediate case for heavy `v`**: `SURV = ∅`, so deficit `0` suffices. -/
theorem gainF2_of_firstJoin_heavy (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hinj : Set.InjOn (firstJoin gates Q v) ((starPts S Q v).erase v : Set (Fin n))) :
    GainF2 gates S Q v := by
  refine gainF2_of_firstJoin gates p hp hg hU hN S out hev Q v hinter hinj ?_
  rw [surv_eq_empty_of_heavy gates S Q v p hp hg hU hN hv]
  exact Finset.disjoint_empty_right _

/-- **ABSORB(v)** (dwV8p, OPEN): the deficit and the surviving `f`-gates are covered by dying gates
outside `F(v)`. -/
def Absorb (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  (∑ w ∈ starSets S Q v, ((S w).card - 1) - (firstJoinSet gates S Q v).card) +
      (firstJoinSet gates S Q v ∩ SURV gates S Q v).card ≤
    ((F2 gates S Q \ F2 gates S (insert v Q)) \ firstJoinSet gates S Q v).card

include hg hU hN in
/-- **ABSORB ⇒ the F2 step.** -/
theorem gainF2_of_absorb (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ y ∈ S w, x y = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1)
    (H : Absorb gates S Q v) : GainF2 gates S Q v := by
  classical
  have hle := card_firstJoinSet_le gates S Q v hinter
  have hFS : firstJoinSet gates S Q v \ SURV gates S Q v ⊆
      (F2 gates S Q \ F2 gates S (insert v Q)) ∩ firstJoinSet gates S Q v := by
    intro i hi
    obtain ⟨hiF, hiS⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_inter.mpr ⟨seeK3_subset_gain gates S Q v (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨firstJoinSet_subset_SEE gates p hp hg hU hN S out hev Q v hiF, hiS⟩)), hiF⟩
  have h1 := Finset.card_le_card hFS
  have h2 := Finset.card_sdiff_add_card_inter (firstJoinSet gates S Q v) (SURV gates S Q v)
  have h3 := Finset.card_sdiff_add_card_inter (F2 gates S Q \ F2 gates S (insert v Q)) (firstJoinSet gates S Q v)
  unfold Absorb at H
  unfold GainF2
  omega

end FirstJoin

end PEqualNP.Outside.L_meta_951_aux
