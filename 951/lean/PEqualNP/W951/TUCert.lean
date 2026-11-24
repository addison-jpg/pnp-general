import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.ConeCert

/-!
# TUCert: (S) of CERT-3c by the real Theorem U

Coord 13:25: prove (S) (the cone merge sets of the sets through `v` are pairwise disjoint). This file
proves (S) from a purely combinatorial condition on the NOT gate and the zero points.

* **Real Theorem U** (`val_le_of_sameNot`): for real points `a ≤ b` at which the NOT gate agrees
  (`h(a) = h(b)`), every wire of the one-NOT circuit is monotone from `a` to `b` (the lift is monotone
  and the real circuit is the lift at `(x, ¬h(x))`).
* `TUPair gates p R z z'`: of every two points `u ≠ u'` of `R`, one, `x`, has `z + e_x ≤ z'` and the
  NOT gate agreeing at `z + e_x` and `z'`.
* `coneMerge_disjoint_of_tu`: `TUPair R z z'` ⇒ the cone merge sets of `R` at `z` and of any `R'` at `z'`
  are disjoint (a gate `0` at `z'` cannot be `1` at a point below `z'` on the same NOT level).
* **`certS_of_tu`**: pairwise `TUPair` in one direction ⇒ `CertS`.
* `tuPair_of_le`: `z ≤ z'`, every point of `R` other than `v` in `z'`, and the NOT gate `1` at `z'`
  (`h(z') = 0`) ⇒ `TUPair R z z'`.
* **The staircase** (`stairPt`): order the sets through `v` by an injective `rank` and put
  `z_w = Q ∪ ⋃_{rank w' < rank w} (S_w' \ {v})`. `certS_stair`: if the NOT gate is `1` at every staircase
  point (`h(z_w) = 0`), (S) holds. **`cert3c_of_stair`**: with (D) at the staircase points this is
  CERT-3c (the staircase points avoid `S_w` by `|S_w ∩ S_w'| ≤ 1`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section TUCert

variable {n m : ℕ}

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **Real Theorem U**: on one level of the NOT gate the real circuit is monotone. -/
theorem val_le_of_sameNot {a b : Fin n → Bool} (hab : a ≤ b)
    (hnot : val gates a (n + p) = val gates b (n + p)) (i : ℕ) : val gates a i ≤ val gates b i := by
  rw [val_lift (n := n) gates p hp a i, val_lift (n := n) gates p hp b i, hnot]
  exact val_le_of_le _ (monoList_lift (n := n) gates p hp hg hU hN).andOr (ext_le_of_le hab le_rfl) _

/-- **The pair condition of the real Theorem U** (`R` at `z` before `z'`). -/
def TUPair (R : Finset (Fin n)) (z z' : Fin n → Bool) : Prop :=
  ∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
    (upPt z u ≤ z' ∧ val gates (upPt z u) (n + p) = val gates z' (n + p)) ∨
      (upPt z u' ≤ z' ∧ val gates (upPt z u') (n + p) = val gates z' (n + p))

include hp hg hU hN in
/-- **Disjointness from the pair condition.** -/
theorem coneMerge_disjoint_of_tu (R R' : Finset (Fin n)) (o o' : ℕ) (z z' : Fin n → Bool)
    (h : TUPair gates p R z z') : Disjoint (coneMerge gates R o z) (coneMerge gates R' o' z') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, rfl, -, -, -, -, u, hu, u', hu', huu, h1, h2⟩ := coneMerge_real gates hg hU hi
  obtain ⟨-, -, -, -, -, hz', -⟩ := coneMerge_real gates hg hU hi'
  rcases h u hu u' hu' huu with ⟨hle, hnot⟩ | ⟨hle, hnot⟩
  · have := val_le_of_sameNot gates p hp hg hU hN hle hnot (n + j)
    rw [h1, hz'] at this
    exact absurd this (by decide)
  · have := val_le_of_sameNot gates p hp hg hU hN hle hnot (n + j)
    rw [h2, hz'] at this
    exact absurd this (by decide)

include hp hg hU hN in
/-- **(S) from the real Theorem U**: if every two sets through `v` satisfy the pair condition in one
direction, their cone merge sets are pairwise disjoint. -/
theorem certS_of_tu (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (z : Fin m → Fin n → Bool)
    (h : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
      TUPair gates p (S w) (z w) (z w') ∨ TUPair gates p (S w') (z w') (z w)) :
    CertS gates S out Q v z := by
  intro w hw w' hw' hww
  rcases h w hw w' hw' hww with h1 | h1
  · exact coneMerge_disjoint_of_tu gates p hp hg hU hN _ _ _ _ _ _ h1
  · exact (coneMerge_disjoint_of_tu gates p hp hg hU hN _ _ _ _ _ _ h1).symm

include hp hg hU hN in
/-- **The pair condition when the NOT gate is `1` at `z'`** (`h(z') = 0`): `z ≤ z'` and every point of
`R` other than `v` lies in `z'`. -/
theorem tuPair_of_le (R : Finset (Fin n)) (v : Fin n) {z z' : Fin n → Bool} (hzz : z ≤ z')
    (hR : ∀ x ∈ R, x ≠ v → z' x = true) (hnot : val gates z' (n + p) = true) :
    TUPair gates p R z z' := by
  have key : ∀ x ∈ R, x ≠ v →
      upPt z x ≤ z' ∧ val gates (upPt z x) (n + p) = val gates z' (n + p) := by
    intro x hx hxv
    have hle : upPt z x ≤ z' := by
      intro c
      by_cases hc : c = x
      · subst hc
        simp [upPt, hR c hx hxv]
      · simp only [upPt, Function.update_of_ne hc]
        exact hzz c
    refine ⟨hle, ?_⟩
    rw [hnot]
    cases hv : val gates (upPt z x) (n + p)
    · have := not_false_of_le gates p hp hg hU hN hle hv
      rw [hnot] at this
      exact absurd this (by decide)
    · rfl
  intro u hu u' hu' huu
  by_cases huv : u = v
  · exact Or.inr (key u' hu' fun h => huu (huv.trans h.symm))
  · exact Or.inl (key u hu huv)

/-! ## The staircase -/

open Classical in
/-- **The staircase zero point** of `w`: `Q` together with `S_w' \ {v}` for every set `w'` through `v`
of smaller rank. -/
noncomputable def stairPt (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (rank : Fin m → ℕ) (w : Fin m) : Fin n → Bool :=
  canonPt (Q ∪ ((starSets S Q v).filter fun w' => rank w' < rank w).biUnion fun w' => (S w').erase v)

theorem stairPt_le (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (rank : Fin m → ℕ)
    {w w' : Fin m} (h : rank w < rank w') : stairPt S Q v rank w ≤ stairPt S Q v rank w' := by
  classical
  refine canonPt_le fun x hx => canonPt_eq_true.mpr ?_
  rcases Finset.mem_union.mp hx with hxQ | hxU
  · exact Finset.mem_union_left _ hxQ
  · obtain ⟨w'', hw'', hx''⟩ := Finset.mem_biUnion.mp hxU
    obtain ⟨hw''s, hr⟩ := Finset.mem_filter.mp hw''
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨w'', Finset.mem_filter.mpr ⟨hw''s, hr.trans h⟩, hx''⟩)

theorem stairPt_mem (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (rank : Fin m → ℕ) {w w' : Fin m} (hw : w ∈ starSets S Q v) (h : rank w < rank w') {x : Fin n}
    (hx : x ∈ S w) (hxv : x ≠ v) : stairPt S Q v rank w' x = true := by
  classical
  exact canonPt_eq_true.mpr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨w, Finset.mem_filter.mpr ⟨hw, h⟩, Finset.mem_erase.mpr ⟨hxv, hx⟩⟩))

theorem stairPt_Q (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (rank : Fin m → ℕ)
    (w : Fin m) {q : Fin n} (hq : q ∈ Q) : stairPt S Q v rank w q = true :=
  canonPt_eq_true.mpr (Finset.mem_union_left _ hq)

/-- The staircase point of a set through `v` avoids the set (`|S_w ∩ S_w'| ≤ 1`). -/
theorem stairPt_off (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (rank : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) {w : Fin m} (hw : w ∈ starSets S Q v)
    {u : Fin n} (hu : u ∈ S w) : stairPt S Q v rank w u = false := by
  classical
  obtain ⟨hwa, hvw⟩ := Finset.mem_filter.mp hw
  have hdis := mem_aliveSets.mp hwa
  cases h : stairPt S Q v rank w u
  · rfl
  · exfalso
    rcases Finset.mem_union.mp (canonPt_eq_true.mp h) with huQ | huU
    · exact Finset.disjoint_left.mp hdis hu huQ
    · obtain ⟨w', hw', hu'⟩ := Finset.mem_biUnion.mp huU
      obtain ⟨hw's, hr⟩ := Finset.mem_filter.mp hw'
      obtain ⟨huv, hu'S⟩ := Finset.mem_erase.mp hu'
      have hww : w' ≠ w := fun h' => (lt_irrefl (rank w)) (h' ▸ hr)
      have hv' : v ∈ S w' := (Finset.mem_filter.mp hw's).2
      have : 1 < (S w' ∩ S w).card := Finset.one_lt_card.mpr
        ⟨u, Finset.mem_inter.mpr ⟨hu'S, hu⟩, v, Finset.mem_inter.mpr ⟨hv', hvw⟩, huv⟩
      have := hS w' w hww
      omega

include hp hg hU hN in
/-- **(S) on the staircase**: if `rank` is injective on the sets through `v` and the NOT gate is `1` at
every staircase point (`h(z_w) = 0`), the cone merge sets at the staircase points are pairwise
disjoint. -/
theorem certS_stair (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n)) (v : Fin n)
    (rank : Fin m → ℕ)
    (hrank : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, rank w = rank w' → w = w')
    (hnot : ∀ w ∈ starSets S Q v, val gates (stairPt S Q v rank w) (n + p) = true) :
    CertS gates S out Q v (stairPt S Q v rank) := by
  refine certS_of_tu gates p hp hg hU hN S out Q v _ fun w hw w' hw' hww => ?_
  rcases lt_trichotomy (rank w) (rank w') with hr | hr | hr
  · exact Or.inl (tuPair_of_le gates p hp hg hU hN (S w) v (stairPt_le S Q v rank hr)
      (fun x hx hxv => stairPt_mem S Q v rank hw hr hx hxv) (hnot w' hw'))
  · exact absurd (hrank w hw w' hw' hr) hww
  · exact Or.inr (tuPair_of_le gates p hp hg hU hN (S w') v (stairPt_le S Q v rank hr)
      (fun x hx hxv => stairPt_mem S Q v rank hw' hr hx hxv) (hnot w hw))

include hp hg hU hN in
/-- **CERT-3c on the staircase**: injective `rank`, `h = 0` at every staircase point and (D) at the
staircase points ⇒ CERT-3c at `v`. -/
theorem cert3c_of_stair (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (v : Fin n) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (rank : Fin m → ℕ)
    (hrank : ∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, rank w = rank w' → w = w')
    (hnot : ∀ w ∈ starSets S Q v, val gates (stairPt S Q v rank w) (n + p) = true)
    (hD : CertD gates S out Q v (stairPt S Q v rank)) : Cert3c gates S out Q v :=
  ⟨stairPt S Q v rank, fun _ hw _ hu => stairPt_off S Q v rank hS hw hu,
    fun w _ _ hq => stairPt_Q S Q v rank w hq, hD,
    certS_stair gates p hp hg hU hN S out Q v rank hrank hnot⟩

end TUCert

end PEqualNP.Outside.L_meta_951_aux
