import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureHall

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

end PEqualNP.Outside.L_meta_951_aux
