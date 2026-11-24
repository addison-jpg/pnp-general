import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureStar
import PEqualNP.W951.PureLLift

/-!
# PureMenu: STAR-SEP / STAR-COUNT over any monotone menu system; Menu2 (front A2, 12:16)

The induction of `PureStar.lean` only uses that the menus shrink as `Q` grows and that every class
is a set of at least `d_w` lifted gates. Here it is stated for an arbitrary MENU SYSTEM
`Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)` (the classes of set `w` allowed at `Q`):

* `StarSepG`, `MenuSDRG`, `menuSDRG_of_starSepG` (STAR-SEP at every `Q` ⇒ an SDR at every `Q`),
  `UQG`, `StarCountG`, `sum_alive_le_UQG` (STAR-COUNT at every `Q` ⇒ `∑_{alive} d_w ≤ |U(Q)|`),
  assuming only `MenuMono Mn` (`Mn (insert v Q) w ⊆ Mn Q w`);
* `MenuSound gates p S Mn`: every class of `Mn ∅ w` has `≥ d_w` gates, all among the
  `gates.length - 1` lifted gates; then `bound_of_menuSDRG`, `bound_of_starCountG` and
  `no_minCE_of_starSepG`, `no_minCE_of_starCountG`.
* **Menu2** (`menu2`): Menu1 (`InMenuQ`) ∪ the real merge sets `M_z(w)` as lifted classes
  (`realLTS`, PureLLift: zero point `(z, ν z)`, atoms `(z + e_u, ν(z + e_u))`) with `Q ⊆ z`,
  `z ∩ S_w = ∅`. `menu2_mono`, `menu2_sound`, `no_minCE_of_starSep2`, `no_minCE_of_starCount2`.
  (`starSep_heavy` stays a Menu1 lemma.)
* L-U_v (front A2): `ltsCls_zero`, `menu2_U_zero` (every gate of `U(Q)` is `0` at `(Q, 0)`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section PureMenu

variable {n m : ℕ}

/-- The menus shrink as `Q` grows. -/
def MenuMono (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) : Prop :=
  ∀ Q v w, Mn (insert v Q) w ⊆ Mn Q w

/-- STAR-SEP over a menu system. -/
def StarSepG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Prop :=
  (aliveSets S Q).Nonempty → ∃ v : Fin n, (starSets S Q v).Nonempty ∧ ∃ K : Fin m → Finset ℕ,
    (∀ w ∈ starSets S Q v, K w ∈ Mn Q w) ∧
    (∀ w ∈ starSets S Q v, ∀ w' ∈ starSets S Q v, w ≠ w' → Disjoint (K w) (K w')) ∧
    ∀ w ∈ starSets S Q v, ∀ w' ∈ aliveSets S Q, v ∉ S w' → ∀ C' ∈ Mn (insert v Q) w', Disjoint (K w) C'

/-- An SDR of the alive sets from the menus at `Q`. -/
def MenuSDRG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Prop :=
  ∃ K : Fin m → Finset ℕ, (∀ w ∈ aliveSets S Q, K w ∈ Mn Q w) ∧
    ∀ w ∈ aliveSets S Q, ∀ w' ∈ aliveSets S Q, w ≠ w' → Disjoint (K w) (K w')

/-- **STAR-SEP ⇒ SDR**, for any monotone menu system. -/
theorem menuSDRG_of_starSepG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (H : ∀ Q, StarSepG S Mn Q) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k → MenuSDRG S Mn Q := by
  classical
  have hempty : ∀ Q, aliveSets S Q = ∅ → MenuSDRG S Mn Q := fun Q h =>
    ⟨fun _ => ∅, fun w hw => by simp [h] at hw, fun w hw => by simp [h] at hw⟩
  intro k
  induction k with
  | zero => intro Q hQ; exact hempty Q (Finset.card_eq_zero.mp (Nat.le_zero.mp hQ))
  | succ k ih =>
    intro Q hQ
    rcases (aliveSets S Q).eq_empty_or_nonempty with h0 | hne
    · exact hempty Q h0
    obtain ⟨v, ⟨w0, hw0⟩, K, hK, hKK, hKo⟩ := H Q hne
    have hw0' := Finset.mem_filter.mp hw0
    have hlt : (aliveSets S (insert v Q)).card < (aliveSets S Q).card := by
      refine Finset.card_lt_card ⟨fun w hw => ((aliveSets_insert S Q v w).mp hw).1, fun hsub => ?_⟩
      exact ((aliveSets_insert S Q v w0).mp (hsub hw0'.1)).2 hw0'.2
    obtain ⟨K', hK'm, hK'd⟩ := ih (insert v Q) (by omega)
    have hstar : ∀ w, w ∈ starSets S Q v ↔ w ∈ aliveSets S Q ∧ v ∈ S w := fun w => Finset.mem_filter
    have hout : ∀ w, w ∈ aliveSets S Q → v ∉ S w → w ∈ aliveSets S (insert v Q) := fun w hw hv =>
      (aliveSets_insert S Q v w).mpr ⟨hw, hv⟩
    refine ⟨fun w => if v ∈ S w then K w else K' w, fun w hw => ?_, fun w hw w' hw' hww => ?_⟩
    · by_cases hv : v ∈ S w
      · simp only [hv, ite_true]; exact hK w ((hstar w).mpr ⟨hw, hv⟩)
      · simp only [hv, ite_false]; exact hmono Q v w (hK'm w (hout w hw hv))
    · by_cases hv : v ∈ S w <;> by_cases hv' : v ∈ S w' <;> simp only [hv, hv', ite_true, ite_false]
      · exact hKK w ((hstar w).mpr ⟨hw, hv⟩) w' ((hstar w').mpr ⟨hw', hv'⟩) hww
      · exact hKo w ((hstar w).mpr ⟨hw, hv⟩) w' hw' hv' (K' w') (hK'm w' (hout w' hw' hv'))
      · exact (hKo w' ((hstar w').mpr ⟨hw', hv'⟩) w hw hv (K' w) (hK'm w (hout w hw hv))).symm
      · exact hK'd w (hout w hw hv) w' (hout w' hw' hv') hww

/-- `U(Q)` for a menu system. -/
def UQG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) : Finset ℕ :=
  (aliveSets S Q).biUnion fun w => (Mn Q w).biUnion id

theorem UQG_insert_subset (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (Q : Finset (Fin n)) (v : Fin n) : UQG S Mn (insert v Q) ⊆ UQG S Mn Q := by
  intro g hg
  simp only [UQG, Finset.mem_biUnion, id] at hg ⊢
  obtain ⟨w, hw, C, hC, hgC⟩ := hg
  exact ⟨w, ((aliveSets_insert S Q v w).mp hw).1, C, hmono Q v w hC, hgC⟩

/-- STAR-COUNT over a menu system. -/
def StarCountG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤ (UQG S Mn Q \ UQG S Mn (insert v Q)).card

/-- **STAR-COUNT ⇒ `∑_{alive} d_w ≤ |U(Q)|`**, for any monotone menu system. -/
theorem sum_alive_le_UQG (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn)
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∀ k (Q : Finset (Fin n)), (aliveSets S Q).card ≤ k →
      ∑ w ∈ aliveSets S Q, ((S w).card - 1) ≤ (UQG S Mn Q).card := by
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
    have hcard := Finset.card_sdiff_add_card_eq_card (UQG_insert_subset S Mn hmono Q v)
    unfold StarCountG starSets at hcount
    omega

/-- Soundness of a menu system at `Q = ∅`: every class has at least `d_w` gates, all among the
lifted gates. -/
def MenuSound (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n))
    (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) : Prop :=
  ∀ w, ∀ C ∈ Mn ∅ w, (S w).card - 1 ≤ C.card ∧ C ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)

theorem aliveSets_empty (S : Fin m → Finset (Fin n)) : aliveSets S ∅ = Finset.univ := by
  ext w; simp [mem_aliveSets]

/-- **An SDR from a sound menu system ⇒ the bound with one gate to spare.** -/
theorem bound_of_menuSDRG (gates : List Gate) (p : ℕ) (hp : p < gates.length) (S : Fin m → Finset (Fin n))
    (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)) (hs : MenuSound gates p S Mn)
    (H : MenuSDRG S Mn ∅) : ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  classical
  obtain ⟨K, hK, hdis⟩ := H
  rw [aliveSets_empty] at hK hdis
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint K :=
    fun w _ w' _ hww => hdis w (Finset.mem_univ _) w' (Finset.mem_univ _) hww
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (K w).card := Finset.sum_le_sum fun w _ => (hs w (K w) (hK w (Finset.mem_univ _))).1
    _ = (Finset.univ.biUnion K).card := (Finset.card_biUnion hpd).symm
    _ ≤ (Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ => (hs w (K w) (hK w (Finset.mem_univ _))).2)
    _ = gates.length - 1 := by rw [Nat.card_Ico, length_lift n p gates hp]; omega

/-- **STAR-COUNT for a sound monotone menu system ⇒ the bound with one gate to spare.** -/
theorem bound_of_starCountG (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (S : Fin m → Finset (Fin n)) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ))
    (hmono : MenuMono Mn) (hs : MenuSound gates p S Mn)
    (H : ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  have h := sum_alive_le_UQG S Mn hmono H _ ∅ le_rfl
  rw [aliveSets_empty] at h
  have hsub : UQG S Mn ∅ ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
    intro g hg
    simp only [UQG, Finset.mem_biUnion, id] at hg
    obtain ⟨w, -, C, hC, hgC⟩ := hg
    exact (hs w C hC).2 hgC
  have h2 := Finset.card_le_card hsub
  rw [Nat.card_Ico, length_lift n p gates hp] at h2
  omega

/-! ## Menu2 (front A2): Menu1 plus the real merge sets as lifted classes -/

open Classical in
/-- **Menu2_Q(w)**: the `Menu1_Q` classes (`InMenuQ`) and the lifted real merge sets
`ltsCls (realLTS z)` with `Q ⊆ z` and `z ∩ S_w = ∅`. -/
noncomputable def menu2 (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n))
    (w : Fin m) : Finset (Finset ℕ) :=
  ((Finset.univ.filter fun s => InMenuQ gates p Q (S w) (optOfSum s)).image
      fun s => pureCls gates p (S w) (optOfSum s)) ∪
    ((Finset.univ.filter fun z : Fin n → Bool => (∀ v ∈ Q, z v = true) ∧ ∀ v ∈ S w, z v = false).image
      fun z => ltsCls gates p (S w) (realLTS gates p z))

theorem mem_menu2 {gates : List Gate} {p : ℕ} {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)}
    {w : Fin m} {C : Finset ℕ} :
    C ∈ menu2 gates p S Q w ↔ (∃ c, InMenuQ gates p Q (S w) c ∧ pureCls gates p (S w) c = C) ∨
      ∃ z : Fin n → Bool, ((∀ v ∈ Q, z v = true) ∧ ∀ v ∈ S w, z v = false) ∧
        ltsCls gates p (S w) (realLTS gates p z) = C := by
  classical
  rw [menu2, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact Or.inl ⟨optOfSum s, (Finset.mem_filter.mp hs).2, rfl⟩
    · exact Or.inr ⟨z, (Finset.mem_filter.mp hz).2, rfl⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨z, hz, rfl⟩)
    · obtain ⟨s, rfl⟩ := optOfSum_surj c
      exact Or.inl ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩
    · exact Or.inr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem menu2_mono (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) :
    MenuMono (menu2 gates p S) := by
  intro Q v w C hC
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨hzQ, hzS⟩, rfl⟩
  · exact mem_menu2.mpr (Or.inl ⟨c, InMenuQ.mono (Finset.subset_insert v Q) hc, rfl⟩)
  · exact mem_menu2.mpr (Or.inr ⟨z, ⟨fun x hx => hzQ x (Finset.mem_insert_of_mem hx), hzS⟩, rfl⟩)

/-- **Menu2 is sound** (Menu1 classes by `card_pureCls`; real merge sets by L-LIFT, `realLTS_valid`). -/
theorem menu2_sound (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (S : Fin m → Finset (Fin n))
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    MenuSound gates p S (menu2 gates p S) := by
  intro w C hC
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨-, hzS⟩, rfl⟩
  · exact ⟨card_pureCls gates p hp hg hU hN (S w) c hc.valid (out w) (hev w),
      pureCls_subset gates p (S w) c⟩
  · exact ⟨card_ltsCls gates p hp hg hU hN (S w) (out w) _
      (realLTS_valid gates p hp hg hU hN (S w) (out w) (hev w) z hzS), ltsCls_subset gates p (S w) _⟩

/-! ## L-U_v (front A2, 12:21): every gate of `U(Q)` is `0` at `(Q, 0)` -/

/-- A gate of a lifted class is `0` at the class's zero point. -/
theorem ltsCls_zero {gates : List Gate} {p : ℕ} {R : Finset (Fin n)} {t : LTS n} {i : ℕ}
    (hi : i ∈ ltsCls gates p R t) : val (lift n p gates) t.zero i = false := by
  classical
  have h := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter] at h
  exact h.2.1

/-- **L-U_v for Menu2**: every gate of `U(Q)` (the Menu2 classes of the sets alive at `Q`) is `0` in
`C_0` at the point `Q` (`(Q, 0)` in the lift). Every Menu2 zero point lies above `(Q, 0)`: `(Z, 1)`
with `Q ⊆ R' ⊆ Z`; `(top_w, 0)` with `Q ∩ S_w = ∅`; `(z, ν z)` with `Q ⊆ z`. Apply it at
`insert v Q` for front's statement about `U(Q ∪ {v})`. -/
theorem menu2_U_zero (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (S : Fin m → Finset (Fin n))
    (Q : Finset (Fin n)) :
    ∀ g ∈ UQG S (menu2 gates p S) Q, val (lift n p gates) (ext (canonPt Q) false) g = false := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  intro g hg'
  simp only [UQG, Finset.mem_biUnion, id] at hg'
  obtain ⟨w, hw, C, hC, hgC⟩ := hg'
  have hQw := mem_aliveSets.mp hw
  -- it suffices that the class's zero point lies above `(Q, 0)`
  have key : ∀ t : LTS n, ext (canonPt Q) false ≤ t.zero → g ∈ ltsCls gates p (S w) t →
      val (lift n p gates) (ext (canonPt Q) false) g = false := fun t hle hgt =>
    val_false_of_le _ hm.andOr hle (ltsCls_zero hgt)
  rcases mem_menu2.mp hC with ⟨c, hc, rfl⟩ | ⟨z, ⟨hzQ, -⟩, rfl⟩
  · rw [pureCls_eq_ltsCls] at hgC
    refine key _ ?_ hgC
    cases c with
    | oneAt Z A =>
      obtain ⟨-, R', -, hQR, hRZ⟩ := hc
      exact ext_le_of_le (canonPt_le fun x hx => hRZ x (hQR hx)) (by decide)
    | zero m' =>
      exact ext_le_of_le (canonPt_le_Zof hQw.symm) le_rfl
    | one Z => exact hc.elim
    | zeroAt z m' => exact hc.elim
  · exact key _ (ext_le_of_le (canonPt_le hzQ) (Bool.false_le _)) hgC

end PureMenu

/-- **951 from STAR-SEP over a sound monotone menu system.** -/
theorem no_minCE_of_starSepG
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (_ : p < gates.length) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)),
        MenuMono Mn ∧ MenuSound gates p S Mn ∧ ∀ Q, StarSepG S Mn Q) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, Mn, hmono, hs, hS⟩ := H n m S gates out M
  have h1 := bound_of_menuSDRG gates p hp S Mn hs (menuSDRG_of_starSepG S Mn hmono hS _ ∅ le_rfl)
  have h2 := M.ce.hlt
  omega

/-- **951 from STAR-COUNT over a sound monotone menu system.** -/
theorem no_minCE_of_starCountG
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (_ : p < gates.length) (Mn : Finset (Fin n) → Fin m → Finset (Finset ℕ)),
        MenuMono Mn ∧ MenuSound gates p S Mn ∧
          ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S Mn Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, Mn, hmono, hs, hS⟩ := H n m S gates out M
  have h1 := bound_of_starCountG gates p hp S Mn hmono hs hS
  have h2 := M.ce.hlt
  omega

/-- **951 from STAR-SEP over Menu2** (front A2). -/
theorem no_minCE_of_starSep2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, StarSepG S (menu2 gates p S) Q) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_starSepG fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, menu2 gates p S, menu2_mono gates p S,
      menu2_sound gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev, hS⟩

/-- **951 from STAR-COUNT over Menu2** (front A2). -/
theorem no_minCE_of_starCount2
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, (aliveSets S Q).Nonempty → ∃ v, (starSets S Q v).Nonempty ∧ StarCountG S (menu2 gates p S) Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_starCountG fun n m S gates out M => by
    obtain ⟨p, hp, hN, hS⟩ := H n m S gates out M
    exact ⟨p, hp, menu2 gates p S, menu2_mono gates p S,
      menu2_sound gates p hp M.ce.hg M.ce.hU hN S out M.ce.hev, hS⟩

end PEqualNP.Outside.L_meta_951_aux
