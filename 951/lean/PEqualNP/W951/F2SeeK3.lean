import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2Desc

/-!
# F2SeeK3: the F2 step from SEE + K3 (dwV8p, `951/PROOF_PLAN_SUGGESTIONS.md` §6)

Notation of §6 (`Q` fixed to `1`, `v` a point): `cost(v) = ∑_{alive w ∋ v} d_w`,
`SEE(v) = {g ∈ F2(Q) : real g(Q + e_v) = 1}`, `SURV(v) = SEE(v) ∩ F2(Q ∪ {v})`,
`K3(v) = {g ∈ F2(Q) : every witness of g at Q belongs to a set through v}`.

**Step 1 (proved there; here).**
* `seeK3_subset_gain`: `(SEE \ SURV) ∪ K3 ⊆ F2(Q) \ F2(Q ∪ {v})` (SEE \ SURV by definition; K3 by Lemma D:
  a witness at `Q ∪ {v}` belongs to a set avoiding `v`, and it is a witness at `Q`).
* `gainF2_of_seeK3`: `SeeK3` (`cost(v) ≤ |(SEE \ SURV) ∪ K3|`) ⇒ `GainF2`.
* `surv_eq_empty_of_heavy`: `SURV(v) = ∅` for `v` heavy over `Q` (F1, `F2Desc`).
* `no_minCE_of_seeK3`: SEE+K3 at some `v ∉ Q` for every `Q` with positive base, in every minimal
  counterexample ⇒ 951.

**Step 2, the proved part (joint union-find).** The real run over `P` = the union of the star sets of
`v`, at zero point `Q` (test points `Q + e_x`):
* `cost_le_card_jointMerge`: with the star sets meeting pairwise in at most one point, it has at least
  `|P| - 1 = cost(v)` merges (every star set ends in `v`'s block).
* `jointMerge_mem_F2`: a joint merge that is `1` at `Q + e_u` and `Q + e_u'` for two points `u ≠ u'` of
  one star set is an `F2(Q)` gate.
REROUTE (the cross merges) is open and not here.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section SeeK3

variable {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)

open Classical in
/-- `SEE(v)`: the `F2(Q)` gates that are `1` at `Q + e_v` in the real circuit. -/
noncomputable def SEE : Finset ℕ :=
  (F2 gates S Q).filter fun i => val gates (canonPt (insert v Q)) i = true

/-- `SURV(v) = SEE(v) ∩ F2(Q ∪ {v})`. -/
noncomputable def SURV : Finset ℕ := SEE gates S Q v ∩ F2 gates S (insert v Q)

open Classical in
/-- `K3(v)`: the `F2(Q)` gates all of whose witnesses at `Q` belong to sets through `v`. -/
noncomputable def K3 : Finset ℕ :=
  (F2 gates S Q).filter fun i => ∀ w ∈ aliveSets S Q, F2Wit gates (S w) Q i → v ∈ S w

/-- **SEE+K3 at `v`**: `cost(v) ≤ |(SEE(v) \ SURV(v)) ∪ K3(v)|`. -/
def SeeK3 : Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ ((SEE gates S Q v \ SURV gates S Q v) ∪ K3 gates S Q v).card

/-- **Both parts lie in the gain** (Lemma D for K3). -/
theorem seeK3_subset_gain :
    (SEE gates S Q v \ SURV gates S Q v) ∪ K3 gates S Q v ⊆
      F2 gates S Q \ F2 gates S (insert v Q) := by
  classical
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · obtain ⟨hsee, hsurv⟩ := Finset.mem_sdiff.mp h
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hsee).1, fun hi' => hsurv ?_⟩
    exact Finset.mem_inter.mpr ⟨hsee, hi'⟩
  · obtain ⟨hF, hK⟩ := Finset.mem_filter.mp h
    refine Finset.mem_sdiff.mpr ⟨hF, fun hi' => ?_⟩
    obtain ⟨-, w, hw, hwit⟩ := mem_F2.mp hi'
    obtain ⟨hwQ, hvw⟩ := (aliveSets_insert S Q v w).mp hw
    exact hvw (hK w hwQ (hwit.mono (Finset.subset_insert v Q)))

/-- **Step 1: SEE+K3 ⇒ the F2 step.** -/
theorem gainF2_of_seeK3 (H : SeeK3 gates S Q v) : GainF2 gates S Q v :=
  H.trans (Finset.card_le_card (seeK3_subset_gain gates S Q v))

/-- **SURV is empty for heavy `v`** (F1). -/
theorem surv_eq_empty_of_heavy (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (hv : val gates (canonPt (insert v Q)) (n + p) = false) : SURV gates S Q v = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  obtain ⟨hsee, hi'⟩ := Finset.mem_inter.mp hi
  have h1 := (Finset.mem_filter.mp hsee).2
  obtain ⟨-, w, -, hwit⟩ := mem_F2.mp hi'
  rw [F1_real_zero gates p hp hg hU hN (S w) Q v hv hwit] at h1
  exact absurd h1 (by decide)

end SeeK3

/-- **951 from SEE+K3** (dwV8p's Step 1): if in every minimal counterexample every `Q` with positive
base has a point `v ∉ Q` with SEE+K3, there is no minimal counterexample. -/
theorem no_minCE_of_seeK3
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∀ Q, 0 < baseDQ S ∅ Q → ∃ v, v ∉ Q ∧ SeeK3 gates S Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_gainF2 fun n m S gates out M Q hQ => by
    obtain ⟨v, hvQ, hv⟩ := H n m S gates out M Q hQ
    exact ⟨v, hvQ, gainF2_of_seeK3 gates S Q v hv⟩

/-! ## Step 2, the proved part: the joint union-find -/

section Joint

variable {n m : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

/-- `P`: the union of the star sets of `v` at `Q`. -/
def starPts (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (starSets S Q v).biUnion S

/-- With the star sets meeting pairwise in at most one point, `|P| = 1 + cost(v)` (star nonempty). -/
theorem card_starPts (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (hne : (starSets S Q v).Nonempty)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1) :
    (starPts S Q v).card = ∑ w ∈ starSets S Q v, ((S w).card - 1) + 1 := by
  classical
  have hvS : ∀ w ∈ starSets S Q v, v ∈ S w := fun w hw => (Finset.mem_filter.mp hw).2
  have hvP : v ∈ starPts S Q v := by
    obtain ⟨w, hw⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨w, hw, hvS w hw⟩
  have herase : (starPts S Q v).erase v = (starSets S Q v).biUnion fun w => (S w).erase v := by
    ext x
    simp only [starPts, Finset.mem_erase, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx, w, hw, hxw⟩
      exact ⟨w, hw, hx, hxw⟩
    · rintro ⟨w, hw, hx, hxw⟩
      exact ⟨hx, w, hw, hxw⟩
  have hpd : ((starSets S Q v : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => (S w).erase v := by
    intro w hw w' hw' hww
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    have hxv := (Finset.mem_erase.mp hx).1
    have hsub : ({v, x} : Finset (Fin n)) ⊆ S w ∩ S w' := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_inter.mpr ⟨hvS w hw, hvS w' hw'⟩
      · rw [Finset.mem_singleton.mp hy]
        exact Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hx).2, (Finset.mem_erase.mp hx').2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hxv)] at this
    have := hinter w hw w' hw' hww
    omega
  have h1 := Finset.card_erase_add_one hvP
  rw [herase, Finset.card_biUnion hpd] at h1
  rw [← h1]
  congr 1
  exact Finset.sum_congr rfl fun w hw => Finset.card_erase_of_mem (hvS w hw)

include hg hU in
/-- **The joint union-find count**: the real run over `P` at zero point `Q` has at least `cost(v)`
merges (each star set ends in one block, all through `v`). -/
theorem cost_le_card_jointMerge (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) (v : Fin n)
    (hinter : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → (S w ∩ S w').card ≤ 1) :
    ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ (mergeSet gates (starPts S Q v) (canonPt Q)).card := by
  classical
  rcases (starSets S Q v).eq_empty_or_nonempty with h0 | hne
  · rw [h0, Finset.sum_empty]
    exact Nat.zero_le _
  set z := canonPt Q
  set P := starPts S Q v
  have hc := run_countT z (upPt z) P gates (fun u _ c => upPt_hT z u c) (goodT_upPt gates hg hU z P)
    gates.length
  have hinv := run_InvT z (upPt z) P gates (fun u _ c => upPt_hT z u c)
  have hvS : ∀ w ∈ starSets S Q v, v ∈ S w := fun w hw => (Finset.mem_filter.mp hw).2
  -- every point of `P` ends in `v`'s block
  have hblock : ∀ x ∈ P, runLT z (upPt z) P gates gates.length x =
      runLT z (upPt z) P gates gates.length v := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
    have hQ := mem_aliveSets.mp (Finset.mem_filter.mp hw).1
    have hz : val gates z (out w) = false := by
      rw [hev]
      simp only [z, canonPt, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
      exact fun y hy hyQ => Finset.disjoint_left.mp hQ hy hyQ
    have hone : ∀ y ∈ S w, val gates (upPt z y) (out w) = true := fun y hy => by
      rw [hev]
      exact decide_eq_true ⟨y, hy, by simp [upPt]⟩
    exact hinv (out w) x v hz (hone x hxw) (hone v (hvS w hw)) hx
      (Finset.mem_biUnion.mpr ⟨w, hw, hvS w hw⟩)
  have h1 : (P.image (runLT z (upPt z) P gates gates.length)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    rw [hblock x hx, hblock y hy]
  have hcard : P.card = ∑ w ∈ starSets S Q v, ((S w).card - 1) + 1 := card_starPts S Q v hne hinter
  unfold mergeSet
  omega

include hg hU in
/-- **A same-set joint merge is an F2(Q) gate**: a merge of the joint run that is `1` at `Q + e_u` and
`Q + e_u'` for two points `u ≠ u'` of one star set has the real witness `(Q, u, u')`. -/
theorem jointMerge_mem_F2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) {i : ℕ}
    (hi : i ∈ mergeSet gates (starPts S Q v) (canonPt Q)) {w : Fin m} (hw : w ∈ starSets S Q v)
    {u u' : Fin n} (hu : u ∈ S w) (hu' : u' ∈ S w) (huu : u ≠ u')
    (h1 : val gates (upPt (canonPt Q) u) i = true) (h2 : val gates (upPt (canonPt Q) u') i = true) :
    i ∈ F2 gates S Q := by
  classical
  obtain ⟨j, -, rfl, -⟩ := (runMT_mem _ _ _ gates gates.length i).mp hi
  obtain ⟨hjl, hor⟩ := mergeSet_or gates hg hU _ _ j hi
  have h0 : val gates (canonPt Q) (n + j) = false := by
    have h := mergeSet_subset_DT gates _ _ hi
    simp only [DT, Finset.mem_filter] at h
    exact h.2.1
  have hwa := (Finset.mem_filter.mp hw).1
  have hZR : ∀ x ∈ S w, canonPt Q x = false := by
    intro x hx
    simp only [canonPt, decide_eq_false_iff_not]
    exact Finset.disjoint_left.mp (mem_aliveSets.mp hwa) hx
  exact mem_F2.mpr ⟨⟨j, rfl, gates[j], List.getElem?_eq_getElem hjl, hor⟩, w, hwa,
    canonPt Q, u, u', hu, hu', huu, hZR, fun x hx => canonPt_eq_true.mpr hx, h0, h1, h2⟩

end Joint

end PEqualNP.Outside.L_meta_951_aux
