import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureHeredity

/-!
# PureGP: SDRs of lifted test systems (front's GP classes, A1-a 11:43) close 951

The most general pure-type target: every set picks a LIFTED TEST SYSTEM in the lift
`lift n p gates` (monotone, on `n + 1` inputs, the last one `y` = the NOT gate), i.e. a zero point
`ζ` and an atom `q c` for every lifted coordinate `c` of `S_w` (`LTS`), with

* `o_w(ζ) = 0` and `o_w(q c) = 1` (lifted output wire), and
* no coordinate false at `ζ` is true at two atoms (`LTSValid`);

its class is the union-find merge set (`runMT`) of that test system (`ltsCls`). Then:

* `merge_countT'`, `card_ltsCls`: every valid class has at least (and at most, `runMT_card_le`)
  `|S_w| - 1` merges. `merge_countT` of `MergeRunT.lean` with the PAIRWISE condition on the
  atoms (its `hT`, "the only coordinate of atom `u` outside `ζ` is `u`", is used only in
  `invKT_zero`).
* `LiftSDR S gates out p`, `bound_of_liftSDR`, `no_minCE_of_liftSDR`: pairwise disjoint classes
  close `no_minCE`.
* `PureOpt.toLTS`, `pureCls_eq_ltsCls` (by `rfl`), `pureValid_ltsValid`, `liftSDR_of_pureSDR`: all four
  pure option kinds (`one`, `zero`, `zeroAt`, `oneAt`) are lifted test systems.
* **GP** (front A1-a): `gpLTS b z A` = zero point `(z, b)`, atoms `(A_u, b)`; `gpLTS_valid`:
  `C_b(o_w)(z) = 0`, `C_b(o_w)(A_u) = 1`, `A_u ∩ A_v ⊆ z` (`u ≠ v`) ⇒ valid. (`u ∈ A_u` is not
  needed.)
* **Theorem U** (`disjoint_gp`): GP classes `(b, z, A)` of `R` and `(b', z', A')` of `R'` are disjoint
  when `b ≤ b'` and of any two atoms `A_u`, `A_v` (`u ≠ v ∈ R`) one lies in `z'`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## The union-find count with pairwise-separated atoms -/

section CountPair

variable {n : ℕ} (z : Fin n → Bool) (q : Fin n → Fin n → Bool) (R : Finset (Fin n)) (gs : List Gate)

theorem invKT_zero' (hT : ∀ c : Fin n, z c = false → ∀ u ∈ R, ∀ v ∈ R, q u c = true → q v c = true → u = v)
    (l : Fin n → Fin n) : InvKT z q R gs 0 l := by
  intro i hi hz u hu v hv hui hvi
  rw [mr_val_take gs _ 0 i hi, List.take_zero, val_nil, dite_eq_left (by omega)] at hui hvi hz
  rw [hT _ hz u hu v hv hui hvi]

theorem runLT_inv' (hT : ∀ c : Fin n, z c = false → ∀ u ∈ R, ∀ v ∈ R, q u c = true → q v c = true → u = v)
    (k : ℕ) : InvKT z q R gs k (runLT z q R gs k) := by
  induction k with
  | zero => exact invKT_zero' z q R gs hT _
  | succ k ih => exact invKT_succ z q R gs _ k ih

theorem run_countT' (hT : ∀ c : Fin n, z c = false → ∀ u ∈ R, ∀ v ∈ R, q u c = true → q v c = true → u = v)
    (hgood : GoodT z q R gs) (k : ℕ) :
    R.card ≤ (R.image (runLT z q R gs k)).card + (runMT z q R gs k).card := by
  induction k with
  | zero => simp [runLT, runMT]
  | succ k ih =>
    by_cases hm : MgT z q R gs (runLT z q R gs k) k
    · have hM : runMT z q R gs (k + 1) = insert (n + k) (runMT z q R gs k) := by
        rw [runMT, ite_eq_left hm]
      have hnot : n + k ∉ runMT z q R gs k := by
        rw [runMT_mem]
        rintro ⟨j, hj, he, -⟩
        omega
      rw [runLT_succ, hM, Finset.card_insert_of_notMem hnot]
      have := img_mergeT z q R gs _ k hm
        (img_le_twoT z q R gs hgood _ k (runLT_inv' z q R gs hT k) hm.1)
      omega
    · have hM : runMT z q R gs (k + 1) = runMT z q R gs k := by
        rw [runMT, ite_eq_right hm]
      rw [runLT_succ, hM, mstepT_nomerge z q R gs hm]
      exact ih

/-- **Lemma M for a general test system with pairwise-separated atoms.** -/
theorem merge_countT' (hT : ∀ c : Fin n, z c = false → ∀ u ∈ R, ∀ v ∈ R, q u c = true → q v c = true → u = v)
    (hgood : GoodT z q R gs) (o : ℕ) (hz : val gs z o = false) (hq : ∀ u ∈ R, val gs (q u) o = true) :
    R.card - 1 ≤ (runMT z q R gs gs.length).card := by
  have hc := run_countT' z q R gs hT hgood gs.length
  have h1 : (R.image (runLT z q R gs gs.length)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hb
    by_cases ho : o < n + gs.length
    · exact runLT_inv' z q R gs hT gs.length o ho hz u hu' v hv' (hq u hu') (hq v hv')
    · have h := hq u hu'
      rw [mr_val_ge gs _ o (by omega)] at h
      exact absurd h (by simp)
  omega

end CountPair

section PureGP

variable {n : ℕ}

/-! ## Lifted test systems -/

/-- A lifted test system: a zero point and an atom for every lifted coordinate. -/
structure LTS (n : ℕ) where
  zero : Fin (n + 1) → Bool
  atom : Fin (n + 1) → Fin (n + 1) → Bool

/-- Its class for the set `R`: the union-find merge set in the lift. -/
noncomputable def ltsCls (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (t : LTS n) : Finset ℕ :=
  runMT t.zero t.atom (liftSet R) (lift n p gates) (lift n p gates).length

/-- Validity for the set `R` with output wire `o` (real numbering). -/
def LTSValid (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (o : ℕ) (t : LTS n) : Prop :=
  val (lift n p gates) t.zero (liftWire n p o) = false ∧
    (∀ c ∈ liftSet R, val (lift n p gates) (t.atom c) (liftWire n p o) = true) ∧
    ∀ x : Fin (n + 1), t.zero x = false →
      ∀ c ∈ liftSet R, ∀ c' ∈ liftSet R, t.atom c x = true → t.atom c' x = true → c = c'

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **Every valid lifted test system has at least `|R| - 1` merges.** -/
theorem card_ltsCls (R : Finset (Fin n)) (o : ℕ) (t : LTS n) (ht : LTSValid gates p R o t) :
    R.card - 1 ≤ (ltsCls gates p R t).card := by
  have := merge_countT' t.zero t.atom (liftSet R) (lift n p gates)
    (fun x hx u hu v hv h1 h2 => ht.2.2 x hx u hu v hv h1 h2)
    (goodT_of_monoList _ _ _ _ (monoList_lift (n := n) gates p hp hg hU hN)) (liftWire n p o) ht.1 ht.2.1
  rwa [card_liftSet] at this

theorem ltsCls_subset (R : Finset (Fin n)) (t : LTS n) :
    ltsCls gates p R t ⊆ Finset.Ico (n + 1) (n + 1 + (lift n p gates).length) := by
  classical
  intro i hi
  have := run_sub_DT t.zero t.atom (liftSet R) (lift n p gates) _ hi
  rw [DT, Finset.mem_filter] at this
  exact this.1

/-- **LiftSDR**: every set picks a valid lifted test system, with pairwise disjoint classes. -/
def LiftSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) (p : ℕ) :
    Prop :=
  ∃ t : Fin m → LTS n, (∀ w, LTSValid gates p (S w) (out w) (t w)) ∧
    ∀ w w', w ≠ w' → Disjoint (ltsCls gates p (S w) (t w)) (ltsCls gates p (S w') (t w'))

include hg hU hN in
/-- **LiftSDR ⇒ the bound with one gate to spare.** -/
theorem bound_of_liftSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (H : LiftSDR S gates out p) : ∑ w, ((S w).card - 1) ≤ gates.length - 1 := by
  classical
  obtain ⟨t, ht, hdis⟩ := H
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      fun w => ltsCls gates p (S w) (t w) := fun w _ w' _ hww => hdis w w' hww
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (ltsCls gates p (S w) (t w)).card :=
        Finset.sum_le_sum fun w _ => card_ltsCls gates p hp hg hU hN (S w) (out w) (t w) (ht w)
    _ = (Finset.univ.biUnion fun w => ltsCls gates p (S w) (t w)).card :=
        (Finset.card_biUnion hpd).symm
    _ ≤ (Finset.Ico (n + 1) (n + 1 + (lift n p gates).length)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun w _ => ltsCls_subset gates p (S w) (t w))
    _ = gates.length - 1 := by rw [Nat.card_Ico, length_lift n p gates hp]; omega

/-! ## The pure options are lifted test systems -/

/-- The lifted test system of a pure option. -/
def PureOpt.toLTS (R : Finset (Fin n)) : PureOpt n → LTS n
  | .one Z => ⟨ext Z true, atom1⟩
  | .zero m => ⟨ext (Zof R) false, atom0 m⟩
  | .zeroAt z m => ⟨ext z false, atom0 m⟩
  | .oneAt Z A => ⟨ext Z true, atom1W A⟩

theorem pureCls_eq_ltsCls (R : Finset (Fin n)) (c : PureOpt n) :
    pureCls gates p R c = ltsCls gates p R (c.toLTS R) := by
  cases c <;> rfl

/-- Per-atom separation (`hT` of `merge_countT`) gives the pairwise one. -/
theorem pairwise_of_perAtom {N : ℕ} (z : Fin N → Bool) (q : Fin N → Fin N → Bool) (R : Finset (Fin N))
    (hT : ∀ c ∈ R, ∀ x : Fin N, q c x = true → z x = false → x = c) :
    ∀ x : Fin N, z x = false → ∀ c ∈ R, ∀ c' ∈ R, q c x = true → q c' x = true → c = c' :=
  fun x hx c hc c' hc' h1 h2 => (hT c hc x h1 hx).symm.trans (hT c' hc' x h2 hx)

include hg hU hN in
/-- **Every valid pure option is a valid lifted test system.** -/
theorem pureValid_ltsValid (R : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) (c : PureOpt n)
    (hc : PureValid gates p R c) : LTSValid gates p R o (c.toLTS R) := by
  -- world 1 at `(Z, 1)` with `Z ∩ R = ∅` and NOT gate `1` at `Z`: the output is `0`
  have hz1 : ∀ Z : Fin n → Bool, (∀ v ∈ R, Z v = false) → val gates Z (n + p) = true →
      val (lift n p gates) (ext Z true) (liftWire n p o) = false := by
    intro Z hZR hZ
    have hl := val_lift (n := n) gates p hp Z o
    rw [hZ, hev] at hl
    rw [← hl]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    rw [hZR v hv] at hzv
    exact absurd hzv (by decide)
  -- world 0 at `(z, 0)` with `z ∩ R = ∅`: the output is `0`
  have hz0 : ∀ z : Fin n → Bool, (∀ v ∈ R, z v = false) →
      val (lift n p gates) (ext z false) (liftWire n p o) = false := by
    intro z hzR
    have h1 := (lift_exact (n := n) gates p hp hg hU hN z o).1
    cases hv : val (lift n p gates) (ext z false) (liftWire n p o)
    · rfl
    · have := h1 hv
      rw [hev] at this
      simp only [decide_eq_true_eq] at this
      obtain ⟨v, hv, hzv⟩ := this
      rw [hzR v hv] at hzv
      exact absurd hzv (by decide)
  -- world 1 atoms `(B, 1)` with `u ∈ B`, `u ∈ R`: the output is `1`
  have ha1 : ∀ u ∈ R, ∀ B : Finset (Fin n), u ∈ B →
      val (lift n p gates) (ext (canonPt B) true) (liftWire n p o) = true := by
    intro u hu B huB
    refine (lift_exact (n := n) gates p hp hg hU hN (canonPt B) o).2.1 ?_
    rw [hev]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr huB⟩
  -- world 0 atoms `(m ∪ {u}, 0)` with NOT gate `0` at `m`: the output is `1`
  have ha0 : ∀ u ∈ R, ∀ m : Finset (Fin n), val gates (canonPt m) (n + p) = false →
      val (lift n p gates) (ext (canonPt (insert u m)) false) (liftWire n p o) = true := by
    intro u hu m hmN
    have hle : canonPt m ≤ canonPt (insert u m) := fun c =>
      Bool.le_iff_imp.mpr fun hc => canonPt_eq_true.mpr (Finset.mem_insert_of_mem (canonPt_eq_true.mp hc))
    have hν := not_false_of_le gates p hp hg hU hN hle hmN
    have hl := val_lift (n := n) gates p hp (canonPt (insert u m)) o
    rw [hν] at hl
    rw [← hl, hev]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_insert_self _ _)⟩
  -- per-atom separation: an atom `(C, b)` with `C ⊆ z ∪ {u}` is true off `(z, b)` only at `u`
  have hsep : ∀ (z : Fin n → Bool) (b : Bool) (u : Fin n) (C : Finset (Fin n)),
      (∀ v ∈ C, v = u ∨ z v = true) → ∀ x : Fin (n + 1), ext (canonPt C) b x = true →
        ext z b x = false → x = Fin.castSucc u := by
    intro z b u C hC x h1 h2
    induction x using Fin.lastCases with
    | last => rw [ext_last] at h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
    | cast v =>
      rw [ext_castSucc, canonPt_eq_true] at h1
      rw [ext_castSucc] at h2
      rcases hC v h1 with rfl | h3
      · rfl
      · rw [h3] at h2; exact absurd h2 (by decide)
  cases c with
  | one Z =>
    obtain ⟨hZR, hZ⟩ := hc
    refine ⟨hz1 Z hZR hZ, fun c hc => ?_, pairwise_of_perAtom _ _ _ fun c hc x h1 h2 => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS]
      rw [atom1_castSucc]
      exact ha1 u hu {u} (Finset.mem_singleton_self u)
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS] at h1 h2
      rw [atom1_castSucc] at h1
      exact hsep Z true u {u} (fun v hv => Or.inl (Finset.mem_singleton.mp hv)) x h1 h2
  | zero m =>
    obtain ⟨hmR, hmN⟩ := hc
    have hzR : ∀ v ∈ R, Zof R v = false := fun v hv => by simp [Zof, hv]
    refine ⟨hz0 (Zof R) hzR, fun c hc => ?_, pairwise_of_perAtom _ _ _ fun c hc x h1 h2 => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS]
      rw [atom0_castSucc]
      exact ha0 u hu (m u) (hmN u hu)
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS] at h1 h2
      rw [atom0_castSucc] at h1
      refine hsep (Zof R) false u (insert u (m u)) (fun v hv => ?_) x h1 h2
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl rfl
      · by_cases hvR : v ∈ R
        · exact Or.inl (hmR u hu v hv hvR)
        · exact Or.inr (by simp [Zof, hvR])
  | zeroAt z m =>
    obtain ⟨hzR, hmz, hmN⟩ := hc
    refine ⟨hz0 z hzR, fun c hc => ?_, pairwise_of_perAtom _ _ _ fun c hc x h1 h2 => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS]
      rw [atom0_castSucc]
      exact ha0 u hu (m u) (hmN u hu)
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS] at h1 h2
      rw [atom0_castSucc] at h1
      refine hsep z false u (insert u (m u)) (fun v hv => ?_) x h1 h2
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact hmz u hu v hv
  | oneAt Z A =>
    obtain ⟨hZR, hZ, hA⟩ := hc
    refine ⟨hz1 Z hZR hZ, fun c hc => ?_, pairwise_of_perAtom _ _ _ fun c hc x h1 h2 => ?_⟩
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS]
      rw [atom1W_castSucc]
      exact ha1 u hu _ (Finset.mem_insert_self u _)
    · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
      simp only [PureOpt.toLTS] at h1 h2
      rw [atom1W_castSucc] at h1
      refine hsep Z true u (insert u (A u)) (fun v hv => ?_) x h1 h2
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact hA u hu v hv

include hg hU hN in
/-- **PureSDR ⇒ LiftSDR.** -/
theorem liftSDR_of_pureSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : PureSDR S gates p) : LiftSDR S gates out p := by
  obtain ⟨c, hc, hdis⟩ := H
  refine ⟨fun w => (c w).toLTS (S w), fun w => pureValid_ltsValid gates p hp hg hU hN (S w) (out w)
    (hev w) (c w) (hc w), fun w w' hww => ?_⟩
  rw [← pureCls_eq_ltsCls, ← pureCls_eq_ltsCls]
  exact hdis w w' hww

/-! ## GP classes (front A1-a) and Theorem U -/

/-- GP atoms in world `b`: the atom of the lifted coordinate `u` is `(A_u, b)`. -/
def atomGP (b : Bool) (A : Fin n → Finset (Fin n)) (c : Fin (n + 1)) : Fin (n + 1) → Bool :=
  if h : c = Fin.last n then canonPt ∅ else ext (canonPt (A (c.castPred h))) b

theorem atomGP_castSucc (b : Bool) (A : Fin n → Finset (Fin n)) (u : Fin n) :
    atomGP b A (Fin.castSucc u) = ext (canonPt (A u)) b := by
  rw [atomGP, dite_eq_right (Fin.castSucc_ne_last u), Fin.castPred_castSucc]

/-- **A GP class**: world `b`, zero point `(z, b)`, atoms `(A_u, b)`. -/
def gpLTS (b : Bool) (z : Fin n → Bool) (A : Fin n → Finset (Fin n)) : LTS n :=
  ⟨ext z b, atomGP b A⟩

/-- **GP validity** (front A1-a): `C_b(o_w)(z) = 0`, `C_b(o_w)(A_u) = 1` for `u ∈ R`, and two atoms
of distinct points of `R` meet only inside `z`. -/
theorem gpLTS_valid (R : Finset (Fin n)) (o : ℕ) (b : Bool) (z : Fin n → Bool)
    (A : Fin n → Finset (Fin n)) (hz : val (lift n p gates) (ext z b) (liftWire n p o) = false)
    (hA : ∀ u ∈ R, val (lift n p gates) (ext (canonPt (A u)) b) (liftWire n p o) = true)
    (hsep : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∀ x ∈ A u, x ∈ A v → z x = true) :
    LTSValid gates p R o (gpLTS b z A) := by
  refine ⟨hz, fun c hc => ?_, fun x hx c hc c' hc' h1 h2 => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    simp only [gpLTS]
    rw [atomGP_castSucc]
    exact hA u hu
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp hc'
    simp only [gpLTS] at hx h1 h2
    rw [atomGP_castSucc] at h1 h2
    by_contra hne
    have huv : u ≠ v := fun h => hne (h ▸ rfl)
    induction x using Fin.lastCases with
    | last =>
      rw [ext_last] at hx h1
      rw [hx] at h1
      exact absurd h1 (by decide)
    | cast x =>
      rw [ext_castSucc] at hx h1 h2
      have := hsep u hu v hv huv x (canonPt_eq_true.mp h1) (canonPt_eq_true.mp h2)
      rw [hx] at this
      exact absurd this (by decide)

include hg hU hN in
/-- **Theorem U** (front A1-a). The GP classes `(b, z, A)` of `R` and `(b', z', A')` of `R'` are
disjoint if `b ≤ b'` and of any two atoms `A_u`, `A_v` (`u ≠ v ∈ R`) one lies in `z'`. -/
theorem disjoint_gp (R R' : Finset (Fin n)) (b b' : Bool) (z z' : Fin n → Bool)
    (A A' : Fin n → Finset (Fin n)) (hb : b ≤ b')
    (hU' : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → (∀ x ∈ A u, z' x = true) ∨ ∀ x ∈ A v, z' x = true) :
    Disjoint (ltsCls gates p R (gpLTS b z A)) (ltsCls gates p R' (gpLTS b' z' A')) := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  simp only [gpLTS]
  rw [atomGP_castSucc, atomGP_castSucc]
  rcases hU' u hu v hv huv with h1 | h1
  · exact Or.inl (ext_le_of_le (canonPt_le h1) hb)
  · exact Or.inr (ext_le_of_le (canonPt_le h1) hb)

end PureGP

/-- **951 from LiftSDR** (the most general pure-type target; contains PureSDR and GP-SDR): if every
minimal counterexample has a NOT gate with a LiftSDR, there is no minimal counterexample. -/
theorem no_minCE_of_liftSDR
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out →
        ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧ LiftSDR S gates out p) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, hN, hP⟩ := H n m S gates out M
  have h1 := bound_of_liftSDR gates p hp M.ce.hg M.ce.hU hN S out hP
  have h2 := M.ce.hlt
  omega

end PEqualNP.Outside.L_meta_951_aux
