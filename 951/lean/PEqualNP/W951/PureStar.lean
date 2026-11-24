import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureHall
import PEqualNP.W951.PureHeredity

/-!
# PureStar: STAR-SEP ⇒ PureSDR (front A2, 11:56)

Front's proposed closing lemma, stated as a HYPOTHESIS (`StarSep`; a conjecture, 0 failures in
front's data), and its induction (PROVED-PAPER there, checked here). For a one-NOT circuit with NOT
gate at `p` and a set `Q` of points:

* `aliveSets S Q`: the sets avoiding `Q`;
* `InMenuQ gates p Q R c` (`Menu1_Q`): `c` is I1 with widened atoms `e_u ∪ R'` for one set `R'` with
  `Q ⊆ R' ⊆ Z` (`oneAt Z A`, `A u = R'`), or I0 at `top_w` with `Q ⊆ m_u` (`zero m`); valid
  (`PureValid`). Monotone in `Q` (`InMenuQ.mono`).
* `StarSep gates p S Q`: if some set is alive, there are a point `v` of an alive set and, for the star
  `St = {alive w : v ∈ S_w}`, options `K_w ∈ Menu1_Q(w)` with pairwise disjoint classes, each disjoint
  from EVERY class of `Menu1_{Q ∪ {v}}(w')` of every alive `w' ∉ St`.

Results: `menuSDR_of_starSep` (STAR-SEP for all `Q` ⇒ for all `Q` the alive sets have a
`Menu1_Q`-SDR; induction on the number of alive sets, using `aliveSets (insert v Q) = aliveSets Q \ St`),
`pureSDR_of_starSep` (`Q = ∅`), `no_minCE_of_starSep`. No minimality and no circuit rebuilding.

Heavy case (front A2, 12:06): `deadPts` (`D`, the points in no alive set), `heavyM`,
`starSep_heavy` (`h(Q ∪ {v}) = 1` and `h(D ∪ {u}) = 1` for the star points `u ≠ v` ⇒ STAR-SEP at `v`),
`starSep_of_hQ` (`h(Q) = 1` ⇒ STAR-SEP at `Q`).

STAR-COUNT (front A2, 12:12): `menuQ`, `UQ` (`U(Q)`, the union of the `Menu1_Q` classes of the alive
sets), `UQ_insert_subset`, `StarCount` (`∑_{star} d_w ≤ |U(Q) \ U(Q ∪ {v})|`), `sum_alive_le_UQ`,
`mu_of_starCount` (STAR-COUNT at every `Q` ⇒ MU), `starCount_of_starSep`, `no_minCE_of_starCount`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureStar

variable {n m : ℕ}

/-- The sets avoiding `Q`. -/
def aliveSets (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun w => Disjoint (S w) Q

/-- The star of `v` among the sets alive at `Q`. -/
def starSets (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Finset (Fin m) :=
  (aliveSets S Q).filter fun w => v ∈ S w

theorem mem_aliveSets {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)} {w : Fin m} :
    w ∈ aliveSets S Q ↔ Disjoint (S w) Q := by
  simp [aliveSets]

theorem aliveSets_insert (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (w : Fin m) :
    w ∈ aliveSets S (insert v Q) ↔ w ∈ aliveSets S Q ∧ v ∉ S w := by
  rw [mem_aliveSets, mem_aliveSets, Finset.disjoint_insert_right]
  exact And.comm

/-- `Menu1_Q(w)` (front A2). -/
def InMenuQ (gates : List Gate) (p : ℕ) (Q R : Finset (Fin n)) : PureOpt n → Prop
  | .oneAt Z A => PureValid gates p R (.oneAt Z A) ∧
      ∃ R' : Finset (Fin n), (∀ u ∈ R, A u = R') ∧ Q ⊆ R' ∧ ∀ v ∈ R', Z v = true
  | .zero m => PureValid gates p R (.zero m) ∧ ∀ u ∈ R, Q ⊆ m u
  | .one _ => False
  | .zeroAt _ _ => False

theorem InMenuQ.valid {gates : List Gate} {p : ℕ} {Q R : Finset (Fin n)} {c : PureOpt n}
    (h : InMenuQ gates p Q R c) : PureValid gates p R c := by
  cases c with
  | oneAt Z A => exact h.1
  | zero m => exact h.1
  | one Z => exact h.elim
  | zeroAt z m => exact h.elim

theorem InMenuQ.mono {gates : List Gate} {p : ℕ} {Q Q' R : Finset (Fin n)} {c : PureOpt n}
    (hQ : Q ⊆ Q') (h : InMenuQ gates p Q' R c) : InMenuQ gates p Q R c := by
  cases c with
  | oneAt Z A =>
    obtain ⟨hv, R', hA, hQR, hRZ⟩ := h
    exact ⟨hv, R', hA, hQ.trans hQR, hRZ⟩
  | zero m => exact ⟨h.1, fun u hu => hQ.trans (h.2 u hu)⟩
  | one Z => exact h.elim
  | zeroAt z m => exact h.elim

/-- **STAR-SEP(C, Q)** (front A2's conjecture, as a hypothesis). -/
def StarSep (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Prop :=
  (aliveSets S Q).Nonempty → ∃ v : Fin n, (starSets S Q v).Nonempty ∧ ∃ K : Fin m → PureOpt n,
    (∀ w ∈ starSets S Q v, InMenuQ gates p Q (S w) (K w)) ∧
    (∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' →
      Disjoint (pureCls gates p (S w) (K w)) (pureCls gates p (S w') (K w'))) ∧
    ∀ w ∈ starSets S Q v, ∀ w' ∈ aliveSets S Q, v ∉ S w' → ∀ c' : PureOpt n,
      InMenuQ gates p (insert v Q) (S w') c' →
        Disjoint (pureCls gates p (S w) (K w)) (pureCls gates p (S w') c')

/-- A `Menu1_Q`-SDR of the sets alive at `Q`. -/
def MenuSDR (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Prop :=
  ∃ c : Fin m → PureOpt n, (∀ w ∈ aliveSets S Q, InMenuQ gates p Q (S w) (c w)) ∧
    ∀ w ∈ aliveSets S Q, ∀ w' ∈ aliveSets S Q, w ≠ w' →
      Disjoint (pureCls gates p (S w) (c w)) (pureCls gates p (S w') (c w'))

theorem menuSDR_of_empty (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (Q : Finset (Fin n)) (h : aliveSets S Q = ∅) : MenuSDR gates p S Q :=
  ⟨fun _ => .one fun _ => false, fun w hw => by simp [h] at hw, fun w hw => by simp [h] at hw⟩

/-- **STAR-SEP ⇒ SDR** (front A2's induction): STAR-SEP at every `Q` gives, for every `Q`, a
`Menu1_Q`-SDR of the alive sets. -/
theorem menuSDR_of_starSep (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, StarSep gates p S Q) : ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k →
      MenuSDR gates p S Q := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hQ
    exact menuSDR_of_empty gates p S Q (Finset.card_eq_zero.mp (Nat.le_zero.mp hQ))
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · exact menuSDR_of_empty gates p S Q h0
    obtain ⟨v, ⟨w0, hw0⟩, K, hK, hKK, hKo⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    -- the sets alive at `insert v Q` are the alive sets outside the star
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    obtain ⟨c', hc'm, hc'd⟩ := ih (insert v Q) (by omega)
    have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
    have hout : ∀ w, w ∈ aliveSets S Q → v ∉ S w → w ∈ aliveSets S (insert v Q) := fun w hw hv =>
      (aliveSets_insert S Q v w).mpr ⟨hw, hv⟩
    refine ⟨fun w => if v ∈ S w then K w else c' w, fun w hw => ?_, fun w hw w' hw' hww => ?_⟩
    · by_cases hv : v ∈ S w
      · simp only [hv, ite_true]
        exact hK w ((hstar w).mpr ⟨hw, hv⟩)
      · simp only [hv, ite_false]
        exact InMenuQ.mono (Finset.subset_insert v Q) (hc'm w (hout w hw hv))
    · by_cases hv : v ∈ S w <;> by_cases hv' : v ∈ S w' <;> simp only [hv, hv', ite_true, ite_false]
      · exact hKK w ((hstar w).mpr ⟨hw, hv⟩) w' ((hstar w').mpr ⟨hw', hv'⟩) hww
      · exact hKo w ((hstar w).mpr ⟨hw, hv⟩) w' hw' hv' (c' w') (hc'm w' (hout w' hw' hv'))
      · exact (hKo w' ((hstar w').mpr ⟨hw', hv'⟩) w hw hv (c' w) (hc'm w (hout w hw hv))).symm
      · exact hc'd w (hout w hw hv) w' (hout w' hw' hv') hww

/-- **STAR-SEP ⇒ PureSDR** (`Q = ∅`: every set is alive, `Menu1_∅` options are valid pure options). -/
theorem pureSDR_of_starSep (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, StarSep gates p S Q) : PureSDR S gates p := by
  have hall : ∀ w, w ∈ aliveSets S ∅ := fun w => mem_aliveSets.mpr (Finset.disjoint_empty_right _)
  obtain ⟨c, hcm, hcd⟩ := menuSDR_of_starSep gates p S H _ ∅ le_rfl
  exact ⟨c, fun w => (hcm w (hall w)).valid, fun w w' hww => hcd w (hall w) w' (hall w') hww⟩

/-! ## The heavy case of STAR-SEP (front A2, 12:06; PROVED-PAPER there, checked here) -/

/-- `D`: the points in no alive set (it contains `Q`). -/
def deadPts (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∀ w ∈ aliveSets S Q, x ∉ S w

theorem subset_deadPts (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Q ⊆ deadPts S Q := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw hxw => ?_⟩
  exact Finset.disjoint_left.mp (mem_aliveSets.mp hw) hxw hx

/-- The heavy-case atom points: `m_v = Q ∪ {v}`, `m_u = D ∪ {u}` for `u ≠ v`. -/
def heavyM (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) (u : Fin n) : Finset (Fin n) :=
  if u = v then insert v Q else insert u (deadPts S Q)

/-- A heavy-case atom `m_u ∪ {u}` avoids every alive set that does not contain `u`. -/
theorem heavyM_disjoint (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v u : Fin n) {w' : Fin m}
    (hw' : w' ∈ aliveSets S Q) (hu : u ∉ S w') : Disjoint (insert u (heavyM S Q v u)) (S w') := by
  rw [Finset.disjoint_left]
  intro x hx hxw
  have hQ := mem_aliveSets.mp hw'
  rw [heavyM] at hx
  split_ifs at hx with huv
  · subst huv
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu hxw
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu hxw
    · exact Finset.disjoint_left.mp hQ hxw hx
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu hxw
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu hxw
    · exact (Finset.mem_filter.mp hx).2 w' hw' hxw

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **STAR-SEP, heavy case** (front A2). If `h(Q ∪ {v}) = 1` and `h(D ∪ {u}) = 1` for every point
`u ≠ v` of the star of `v` (the NOT gate is `0` there), STAR-SEP holds at `v`, with every star set
taking the I0 class at `top_w` with atoms `Q ∪ {v}` and `D ∪ {u}`. No world-1 option lives in the cube
`Q ∪ {v}` (`h = 1` there), and a star class meets any other alive set's world-0 class only if two
of its atoms meet that set, which `|S_w ∩ S_w'| ≤ 1` excludes (W0, `disjoint_pureI0_pureI0`). -/
theorem starSep_heavy (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (Q : Finset (Fin n)) (v : Fin n)
    (hv : (starSets S Q v).Nonempty)
    (hQv : val gates (canonPt (insert v Q)) (n + p) = false)
    (hD : ∀ w ∈ starSets S Q v, ∀ u ∈ S w, u ≠ v →
      val gates (canonPt (insert u (deadPts S Q))) (n + p) = false) :
    StarSep gates p S Q := by
  classical
  intro _
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  -- the star option is valid and in `Menu1_Q`
  have hmenu : ∀ w ∈ starSets S Q v, InMenuQ gates p Q (S w) (.zero (heavyM S Q v)) := by
    intro w hw
    obtain ⟨hwa, -⟩ := (hstar w).mp hw
    have hQw := mem_aliveSets.mp hwa
    refine ⟨⟨fun u hu x hx hxw => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · rw [heavyM] at hx
      split_ifs at hx with huv
      · subst huv
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rfl
        · exact absurd hx (Finset.disjoint_left.mp hQw hxw)
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · rfl
        · exact absurd hxw ((Finset.mem_filter.mp hx).2 w hwa)
    · rw [heavyM]
      split_ifs with huv
      · subst huv; exact hQv
      · exact hD w hw u hu huv
    · rw [heavyM]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact (subset_deadPts S Q).trans (Finset.subset_insert _ _)
  -- the W0 pair condition against any alive set
  have hpair : ∀ w ∈ starSets S Q v, ∀ w' ∈ aliveSets S Q, w ≠ w' →
      ∀ u ∈ S w, ∀ u' ∈ S w, u ≠ u' →
        Disjoint (insert u (heavyM S Q v u)) (S w') ∨ Disjoint (insert u' (heavyM S Q v u')) (S w') :=
    fun w _ w' hw' hww => pair_true_of_inter (S w) (S w') (hS w w' hww) _
      fun u hu => heavyM_disjoint S Q v u hw' hu
  refine ⟨v, hv, fun _ => .zero (heavyM S Q v), hmenu, fun w hw w' hw' hww => ?_, fun w hw w' hw' hvw' c' hc' => ?_⟩
  · exact disjoint_pureI0_pureI0 gates p hp hg hU hN (S w) (S w') _ _
      (hpair w hw w' ((hstar w').mp hw').1 hww)
  · have hww : w ≠ w' := fun h => hvw' (h ▸ ((hstar w).mp hw).2)
    cases c' with
    | zero m' =>
      exact disjoint_pureI0_pureI0 gates p hp hg hU hN (S w) (S w') _ _ (hpair w hw w' hw' hww)
    | oneAt Z A =>
      exfalso
      obtain ⟨⟨-, hZ, -⟩, R', -, hQR, hRZ⟩ := hc'
      have hle : canonPt (insert v Q) ≤ Z := canonPt_le fun x hx => hRZ x (hQR hx)
      have := not_false_of_le gates p hp hg hU hN hle hQv
      rw [hZ] at this
      exact absurd this (by decide)
    | one Z => exact hc'.elim
    | zeroAt z m' => exact hc'.elim

include hg hU hN in
/-- **Corollary** (front A2): `h(Q) = 1` (the NOT gate is `0` at `Q`) ⇒ STAR-SEP at `Q` (every point
`v` of an alive set works). -/
theorem starSep_of_hQ (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (hne : ∀ w, (S w).Nonempty)
    (Q : Finset (Fin n)) (hQ : val gates (canonPt Q) (n + p) = false) : StarSep gates p S Q := by
  intro halive
  obtain ⟨w, hw⟩ := halive
  obtain ⟨v, hv⟩ := hne w
  have hmono : ∀ A : Finset (Fin n), Q ⊆ A → val gates (canonPt A) (n + p) = false := fun A hA =>
    not_false_of_le gates p hp hg hU hN (canonPt_le fun x hx => canonPt_eq_true.mpr (hA hx)) hQ
  exact starSep_heavy gates p hp hg hU hN S hS Q v ⟨w, Finset.mem_filter.mpr ⟨hw, hv⟩⟩
    (hmono _ (Finset.subset_insert _ _))
    (fun _ _ u _ _ => hmono _ ((subset_deadPts S Q).trans (Finset.subset_insert _ _))) ⟨w, hw⟩

/-! ## STAR-COUNT (front A2, 12:12): the counting form of STAR-SEP -/

open Classical in
/-- The union of the `Menu1_Q` classes of `R`. -/
noncomputable def menuQ (gates : List Gate) (p : ℕ) (Q R : Finset (Fin n)) : Finset ℕ :=
  (Finset.univ.filter fun s => InMenuQ gates p Q R (optOfSum s)).biUnion
    fun s => pureCls gates p R (optOfSum s)

theorem mem_menuQ {gates : List Gate} {p : ℕ} {Q R : Finset (Fin n)} {g : ℕ} :
    g ∈ menuQ gates p Q R ↔ ∃ c, InMenuQ gates p Q R c ∧ g ∈ pureCls gates p R c := by
  classical
  rw [menuQ, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hg⟩
    exact ⟨optOfSum s, (Finset.mem_filter.mp hs).2, hg⟩
  · rintro ⟨c, hc, hg⟩
    obtain ⟨s, rfl⟩ := optOfSum_surj c
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hg⟩

/-- `U(Q)`: the union of all `Menu1_Q` classes of the sets alive at `Q`. -/
noncomputable def UQ (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) :
    Finset ℕ :=
  (aliveSets S Q).biUnion fun w => menuQ gates p Q (S w)

theorem mem_UQ {gates : List Gate} {p : ℕ} {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)} {g : ℕ} :
    g ∈ UQ gates p S Q ↔ ∃ w ∈ aliveSets S Q, ∃ c, InMenuQ gates p Q (S w) c ∧ g ∈ pureCls gates p (S w) c := by
  rw [UQ, Finset.mem_biUnion]
  exact ⟨fun ⟨w, hw, hg⟩ => ⟨w, hw, mem_menuQ.mp hg⟩, fun ⟨w, hw, hg⟩ => ⟨w, hw, mem_menuQ.mpr hg⟩⟩

/-- `U(Q ∪ {v}) ⊆ U(Q)`: fewer alive sets, smaller menus. -/
theorem UQ_insert_subset (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n))
    (v : Fin n) : UQ gates p S (insert v Q) ⊆ UQ gates p S Q := by
  intro g hg
  obtain ⟨w, hw, c, hc, hgc⟩ := mem_UQ.mp hg
  exact mem_UQ.mpr ⟨w, ((aliveSets_insert S Q v w).mp hw).1, c,
    InMenuQ.mono (Finset.subset_insert v Q) hc, hgc⟩

/-- **STAR-COUNT(C, Q, v)**: `∑_{w ∈ star(v)} d_w ≤ |U(Q) \ U(Q ∪ {v})|`. -/
def StarCount (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ (UQ gates p S Q \ UQ gates p S (insert v Q)).card

/-- **(a) STAR-COUNT at every `Q` ⇒ `∑_{alive at Q} d_w ≤ |U(Q)|`** (induction on the alive sets). -/
theorem sum_alive_le_UQ (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCount gates p S Q v) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k →
      ∑ w ∈ aliveSets S Q, ((S w).card - 1) ≤ (UQ gates p S Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hQ
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hQ), Finset.sum_empty]
    exact Nat.zero_le _
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.sum_empty]; exact Nat.zero_le _
    obtain ⟨v, ⟨w0, hw0⟩, hcount⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    have hsplit : (aliveSets S Q).filter (fun w => v ∉ S w) = aliveSets S (insert v Q) := by
      ext w
      rw [Finset.mem_filter, aliveSets_insert]
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    have hih := ih (insert v Q) (by omega)
    rw [← Finset.sum_filter_add_sum_filter_not (aliveSets S Q) (fun w => v ∈ S w), hsplit]
    have hcard := Finset.card_sdiff_add_card_eq_card (UQ_insert_subset gates p S Q v)
    unfold StarCount starSets at hcount
    omega

/-- **(a) STAR-COUNT ⇒ MU.** -/
theorem mu_of_starCount (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCount gates p S Q v) :
    MU S gates p := by
  classical
  have hall : aliveSets S ∅ = Finset.univ := by
    ext w; simp [mem_aliveSets]
  have h := sum_alive_le_UQ gates p S H _ ∅ le_rfl
  rw [hall] at h
  refine h.trans (Finset.card_le_card fun g hg => ?_)
  obtain ⟨w, -, c, hc, hgc⟩ := mem_UQ.mp hg
  exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, mem_pureMenu.mpr ⟨c, hc.valid, hgc⟩⟩

include hg hU hN in
/-- **(b) STAR-SEP ⇒ STAR-COUNT**: the star classes are pairwise disjoint, lie in `U(Q)`, avoid
`U(Q ∪ {v})`, and each has at least `d_w` gates. -/
theorem starCount_of_starSep (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (Q : Finset (Fin n)) (H : StarSep gates p S Q) (hne : (aliveSets S Q).Nonempty) :
    ∃ v, (starSets S Q v).Nonempty ∧ StarCount gates p S Q v := by
  classical
  obtain ⟨v, hv, K, hK, hKK, hKo⟩ := H hne
  refine ⟨v, hv, ?_⟩
  have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
  have hpd : ((starSets S Q v : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => pureCls gates p (S w) (K w) := fun w hw w' hw' hww => hKK w hw w' hw' hww
  unfold StarCount
  calc ∑ w ∈ starSets S Q v, ((S w).card - 1)
      ≤ ∑ w ∈ starSets S Q v, (pureCls gates p (S w) (K w)).card :=
        Finset.sum_le_sum fun w hw =>
          card_pureCls gates p hp hg hU hN (S w) (K w) (hK w hw).valid (out w) (hev w)
    _ = ((starSets S Q v).biUnion fun w => pureCls gates p (S w) (K w)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (UQ gates p S Q \ UQ gates p S (insert v Q)).card := by
        refine Finset.card_le_card (Finset.biUnion_subset.mpr fun w hw g hgw => ?_)
        refine Finset.mem_sdiff.mpr ⟨mem_UQ.mpr ⟨w, ((hstar w).mp hw).1, K w, hK w hw, hgw⟩, fun hg' => ?_⟩
        obtain ⟨w', hw', c', hc', hgc'⟩ := mem_UQ.mp hg'
        obtain ⟨hw'a, hvw'⟩ := (aliveSets_insert S Q v w').mp hw'
        exact Finset.disjoint_left.mp (hKo w hw w' hw'a hvw' c' hc') hgw hgc'

end PureStar

/-- **951 from STAR-SEP**: if every minimal counterexample has a NOT gate for which STAR-SEP holds at
every `Q`, there is no minimal counterexample. -/
theorem no_minCE_of_starSep
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, StarSep gates p S Q) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_pureSDR fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, hN, pureSDR_of_starSep gates p S hS⟩

/-- **951 from STAR-COUNT** (front A2): if every minimal counterexample has a NOT gate for which, at
every `Q` with an alive set, some point `v` of an alive set satisfies STAR-COUNT, there is no minimal
counterexample. -/
theorem no_minCE_of_starCount
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCount gates p S Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_MU fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, hN, mu_of_starCount gates p S hS⟩

end PEqualNP.Outside.L_meta_951_aux
