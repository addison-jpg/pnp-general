import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LiftFrac
import PEqualNP.W951.PureLLift
import PEqualNP.W951.Augment
import PEqualNP.W951.LiftBound
import PEqualNP.W951.CanonClass
import PEqualNP.W951.CanonOneNot
import PEqualNP.W951.Lift
import PEqualNP.W951.LiftHelpers
import PEqualNP.W951.Cases
import PEqualNP.W951.MergeFrac

section LiftFJ

/-!
# Conjecture FJ (joint two-world statement at function level) and its case `h = x_p`

`FJfor h` : for every (1,1)-disjoint system `S` on `n` variables, every monotone circuit over
`(x, y)` (`y` = input number `n`) whose outputs lie in `[o_w ∧ (y ∨ h), o_w ∨ (y ∧ h)]` has at least
`∑ (|S w| - 1)` gates.  `h` is any Boolean function: it is not required to be a wire.

`FJ` : `FJfor h` for every monotone `h`.

* `liftedBound_of_FJ : FJ → LiftedBound`, `no_minCE_of_FJ`, `L_meta_951_of_FJ`.
* `oneNot_strict_of_FJ` : FJ gives `∑ (|S w| - 1) ≤ gates.length - 1` for every circuit with a NOT
  gate (`s ≥ base + 1`).
* `FJfor_var p : FJfor (fun x => x p)` (R11 of front-match w9/r_fable.md): configurations
  `Z_w = {(x, 1) : x avoids S_w ∪ {p}}`, atoms `(e_u, 1)` for `u ≠ p` and `(e_p, 0)`; S2.1
  hypotheses and pairwise blocking, then `lift_family_le_length`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- FJ for one function `h`. -/
def FJfor {n : ℕ} (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ (m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gs : List Gate) (out : Fin m → ℕ), MonoList gs →
    (∀ (w : Fin m) (x : Fin n → Bool) (y : Bool),
      InInterval (decide (∃ v ∈ S w, x v = true)) y (h x) (val gs (ext x y) (out w))) →
    ∑ i : Fin m, ((S i).card - 1) ≤ gs.length

/-- **Conjecture FJ**: `FJfor h` for every monotone `h`. -/
def FJ : Prop := ∀ (n : ℕ) (h : (Fin n → Bool) → Bool), Monotone h → FJfor h

/-! ## FJ implies the lifted bound -/

theorem ext_le_ext {n : ℕ} {x x' : Fin n → Bool} {y y' : Bool}
    (hx : ∀ c, x c = true → x' c = true) (hy : y = true → y' = true) : ext x y ≤ ext x' y' := by
  intro c
  unfold ext
  split_ifs with h
  · exact Bool.le_iff_imp.mpr (hx _)
  · exact Bool.le_iff_imp.mpr hy

theorem imp_of_le {n : ℕ} {x x' : Fin n → Bool} (h : x ≤ x') : ∀ c, x c = true → x' c = true :=
  fun c => Bool.le_iff_imp.mp (h c)

theorem liftedBound_of_FJ (H : FJ) : LiftedBound := by
  intro n m S h2 hS pre post hw out hg hy hhw hint
  have hfree : ∀ (x : Fin n → Bool) (y : Bool), val pre (ext x y) hw = val pre (ext x false) hw := by
    intro x y
    rw [← val_unsh pre hy x y hw hhw, ← val_unsh pre hy x false hw hhw]
  have hmono : Monotone fun x : Fin n → Bool => val pre (ext x false) hw := by
    intro x x' hxx
    apply Bool.le_iff_imp.mpr
    exact mono_val pre (fun g hm => (hg g (List.mem_append_left _ hm)).1) _ _
      (imp_of_le (ext_le_ext (imp_of_le hxx) id)) hw
  have := H n _ hmono m S h2 hS (pre ++ post) out hg (fun w x y => by
    have := hint w x y
    rwa [hfree] at this)
  omega

/-- FJ closes 951. -/
theorem no_minCE_of_FJ (H : FJ) {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) : ¬ MinCE S gates out :=
  no_minCE_of_liftedBound (liftedBound_of_FJ H) S gates out

/-- FJ gives `s ≥ base + 1` for every circuit with (exactly) one NOT gate. -/
theorem oneNot_strict_of_FJ (H : FJ) {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length - 1 := by
  have hops := lift_ops (n := n) gates p hp hg hU hN
  have hmono : Monotone fun x : Fin n → Bool => val (gates.take p) x (notIn n p gates) := by
    intro x x' hxx
    apply Bool.le_iff_imp.mpr
    show val (gates.take p) x (notIn n p gates) = true →
      val (gates.take p) x' (notIn n p gates) = true
    rw [← val_shift (gates.take p) x false, ← val_shift (gates.take p) x' false]
    exact mono_val _ (fun g hm => (hops g (List.mem_append_left _ hm)).1) _ _
      (imp_of_le (ext_le_ext (imp_of_le hxx) id)) _
  have := H n _ hmono m S h2 hS (lift n p gates) (fun w => liftWire n p (out w)) hops
    (fun w x y => lift_interval S gates out p hp hg hU hN hev w x y)
  rwa [length_lift n p gates hp] at this

/-- L-meta-951 (same statement as `PEqualNP.Outside.L_meta_951`) from FJ. -/
theorem L_meta_951_of_FJ (H : FJ) : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length :=
  L_meta_951_of_liftedBound (liftedBound_of_FJ H)

/-! ## FJ for `h = x_p` -/

open Classical in
/-- `{(x, 1) : x avoids T}`. -/
noncomputable def fjZ {n : ℕ} (T : Finset (Fin n)) : Finset (Fin (n + 1) → Bool) :=
  (Finset.univ.filter fun x : Fin n → Bool => ∀ v ∈ T, x v = false).image fun x => ext x true

theorem mem_fjZ {n : ℕ} {T : Finset (Fin n)} {z : Fin (n + 1) → Bool} :
    z ∈ fjZ T ↔ ∃ x : Fin n → Bool, (∀ v ∈ T, x v = false) ∧ ext x true = z := by
  simp [fjZ]

/-- The atom of the variable `e`: `(e_e, 1)` for `e ≠ p`, `(e_p, 0)` for `e = p`. -/
def fjAtom {n : ℕ} (p e : Fin n) : Fin (n + 1) → Bool :=
  if e = p then ext (eof p) false else ext (eof e) true

theorem fjAtom_true {n : ℕ} (p e : Fin n) (c : Fin (n + 1)) (hc : (c : ℕ) < n)
    (h : fjAtom p e c = true) : e = ⟨c, hc⟩ := by
  unfold fjAtom at h
  split_ifs at h with hep
  · simp only [ext, hc, dite_true, eof, decide_eq_true_eq] at h
    rw [hep, h]
  · simp only [ext, hc, dite_true, eof, decide_eq_true_eq] at h
    exact h.symm

theorem zof_mem_fjZ {n : ℕ} (T : Finset (Fin n)) : ext (Zof T) true ∈ fjZ T :=
  mem_fjZ.mpr ⟨Zof T, fun v hv => by simp [Zof, hv], rfl⟩

theorem fjZ_join {n : ℕ} (T : Finset (Fin n)) :
    ∀ x ∈ fjZ T, ∀ y ∈ fjZ T, x ⊔ y ∈ fjZ T := by
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := mem_fjZ.mp hz
  obtain ⟨x', hx', rfl⟩ := mem_fjZ.mp hz'
  refine mem_fjZ.mpr ⟨x ⊔ x', fun v hv => by simp [hx v hv, hx' v hv], ?_⟩
  funext c
  simp only [ext, Pi.sup_apply]
  split_ifs <;> simp

/-- Blocking: the atoms of `A` blocked by `fjZ (insert p B)` are indexed by `A ∩ B`, when
`p ∈ A → p ∈ B`. -/
theorem fj_block {n : ℕ} (p : Fin n) (A B : Finset (Fin n)) (hAB : (A ∩ B).card ≤ 1)
    (hp : p ∈ A → p ∈ B) :
    (blockP (fjZ (insert p B)) fun t => fjAtom p (A.orderEmbOfFin rfl t)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card_of_injOn (fun t => A.orderEmbOfFin rfl t) ?_
    (fun s _ t _ h => (A.orderEmbOfFin rfl).injective h)) hAB
  intro t ht
  have hA : A.orderEmbOfFin rfl t ∈ A := Finset.orderEmbOfFin_mem A rfl t
  rw [Finset.mem_coe, Finset.mem_inter]
  refine ⟨hA, ?_⟩
  show A.orderEmbOfFin rfl t ∈ B
  by_contra hB
  have hne : A.orderEmbOfFin rfl t ≠ p := by
    intro h
    rw [h] at hA hB
    exact hB (hp hA)
  refine mem_blockP.mp ht _ (zof_mem_fjZ (insert p B)) ?_
  simp only [fjAtom, ite_eq_right hne]
  refine ext_le_ext (fun c hc => ?_) id
  simp only [eof, decide_eq_true_eq] at hc
  subst hc
  simp [Zof, hne, hB]

/-- **FJ for `h = x_p`** (R11): the lifted form of Theorem X, `h` not required to be a wire. -/
theorem FJfor_var {n : ℕ} (p : Fin n) : FJfor fun x : Fin n → Bool => x p := by
  intro m S h2 hS gs out hm hint
  refine lift_family_le_length gs hm Finset.univ (fun w : Fin m => (S w).card)
    (fun w => fjZ (insert p (S w)))
    (fun w t => fjAtom p ((S w).orderEmbOfFin rfl t)) out
    (fun w _ => ⟨_, zof_mem_fjZ _⟩) (fun w _ => fjZ_join _) ?_ ?_ ?_ ?_
  · -- hL
    intro w _ c hc s t hs ht
    have h0 := hc _ (zof_mem_fjZ (insert p (S w)))
    have hcn : (c : ℕ) < n := by
      by_contra hcn
      simp [ext, hcn] at h0
    have e1 := fjAtom_true p _ c hcn hs
    have e2 := fjAtom_true p _ c hcn ht
    exact (S w).orderEmbOfFin rfl |>.injective (e1.trans e2.symm)
  · -- hZo
    intro w _ z hz
    obtain ⟨x, hx, rfl⟩ := mem_fjZ.mp hz
    by_contra hF
    rw [Bool.not_eq_false] at hF
    have := (hint w x true).2 hF
    have hxp : x p = false := hx p (Finset.mem_insert_self _ _)
    simp only [hxp, Bool.and_false, Bool.or_false, decide_eq_true_eq] at this
    obtain ⟨v, hv, hxv⟩ := this
    rw [hx v (Finset.mem_insert_of_mem hv)] at hxv
    cases hxv
  · -- hao
    intro w _ t
    have hmem : (S w).orderEmbOfFin rfl t ∈ S w := Finset.orderEmbOfFin_mem _ rfl t
    unfold fjAtom
    split_ifs with hep
    · apply (hint w (eof p) false).1
      have : decide (∃ v ∈ S w, eof p v = true) = true :=
        decide_eq_true ⟨p, hep ▸ hmem, by simp [eof]⟩
      rw [this]
      simp [eof]
    · apply (hint w (eof ((S w).orderEmbOfFin rfl t)) true).1
      have : decide (∃ v ∈ S w, eof ((S w).orderEmbOfFin rfl t) v = true) = true :=
        decide_eq_true ⟨_, hmem, by simp [eof]⟩
      rw [this]
      simp
  · -- hblock
    intro u _ v _ huv
    by_cases h : p ∈ S u → p ∈ S v
    · exact Or.inl (fj_block p (S u) (S v) (hS u v huv) h)
    · refine Or.inr (fj_block p (S v) (S u) (hS v u (Ne.symm huv)) fun hv => ?_)
      by_contra
      exact h fun _ => hv

end PEqualNP.Outside.L_meta_951_aux

end LiftFJ

section TwoGateLift

/-!
# TwoGateLift: front A1's Theorem 2G-LIFT (refereed 12:31, desktop Coord)

The two-gate case of the lifted price inequality. For a one-NOT circuit (NOT gate at `p`, `ν x` its
value) with `|S_i ∩ S_j| ≤ 1`, two gates `g, g'` and `m_w = min_{z zero point of S_w} |M_z(w) ∩ {g, g'}|`
(real merge sets): `∑_w m_w ≤ 2`, provided every triple of sets satisfies condition `C(b)` for some `b`.

**Condition `C(b)`** for a triple `S_i, S_j, S_k`, `U = S_i ∪ S_j ∪ S_k`, `b` vanishing on `U`,
`X_l = b ∪ (U \ S_l)` (`ceilPt`): for each `l` of the triple, `h(X_l) = 0` (the NOT gate is `1` at
`X_l`) or `h(b + e_u) = 1` for every `u ∈ U \ S_l`.

**Core** (`twoGate_triple`): under `C(b)` no three distinct sets can each meet `{g, g'}` in every
merge set. Steps (front's §9, all in the lifted monotone circuit through `val_lift`):
* ceilings: the merge set of `w_l` at `X_l` contains `G_l ∈ {g, g'}`, `0` at `P_l = (X_l, ν X_l)`, hence
  `0` at every point below `P_l` (`low_of_below`);
* pigeonhole: a base merge `H_a ∈ M_b(w_a)` is never low at `X_c`, `c ≠ a` (`notLow_base`), so
  `G_i = G_j = G_k = γ` and `H_i = H_j = H_k = γ' ≠ γ`;
* triangle: `γ'` is `1` at `b + e_c` (`c ∈ S_l`) only for `c` in a second set of the triple
  (`triangle`);
* odd cycle: one cover `(a₀, b₀)` of the merge gate `γ'` (`mr_coverT` over all points) and the
  union-find invariant split the two trace points of every run (`run_split`); the three runs give
  three pairwise distinct Booleans.

**Full statement** (`twoGate_lift`): `minHit gates S w g g' = m_w`; case A (some `m_w = 2`: both gates
are universal merges of `w`, so `m_v = 0` for `v ≠ w` by `disjoint_univMergeSet` at `Zof (S_v ∪ S_w)`),
case B (all `m_w ≤ 1`: at most two sets have `m_w = 1` by `twoGate_triple`). Uses only the one-NOT
structure, `|S_i ∩ S_j| ≤ 1` and `C(b)`: no correctness of the outputs, no `|S_w| ≥ 2`, no minimality.
Real merge sets are lifted classes (`mergeSet_eq_lift`), so this is a two-gate price inequality on a
sub-menu of `liftMenu` (MUL / LiftSDR).

Special cases (front §§8–9): `condB_of_hb`, `twoGate_of_hY` (`h(¬∪S) = 1`), `twoGate_of_heavy` (all points
heavy), `twoGate_of_typeB` (all three sets type B relative to the triple). Open (front §9): triples
where for every `b` some set has `h(X_l) = 1` and a light foreign point (cxT2's triple).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section TwoGate

variable {n m : ℕ}

/-- `X_l = b ∪ (U \ S_l)`. -/
def ceilPt (b : Fin n → Bool) (U Sl : Finset (Fin n)) : Fin n → Bool :=
  fun c => b c || decide (c ∈ U ∧ c ∉ Sl)

theorem ceilPt_zero {b : Fin n → Bool} {U Sl : Finset (Fin n)} (hb : ∀ v ∈ U, b v = false)
    (hSU : Sl ⊆ U) : ∀ v ∈ Sl, ceilPt b U Sl v = false := by
  intro v hv
  simp [ceilPt, hb v (hSU hv), hv]

theorem upPt_le_ceilPt {b : Fin n → Bool} {U Sl : Finset (Fin n)} {u : Fin n} (hu : u ∈ U)
    (hul : u ∉ Sl) : upPt b u ≤ ceilPt b U Sl := by
  intro c
  refine Bool.le_iff_imp.mpr fun h => ?_
  by_cases hc : c = u
  · subst hc; simp [ceilPt, hu, hul]
  · rw [upPt, Function.update_of_ne hc] at h
    simp [ceilPt, h]

theorem upPt2_le_ceilPt {b : Fin n → Bool} {U Sl : Finset (Fin n)} {c u : Fin n} (hc : c ∈ U)
    (hcl : c ∉ Sl) (hu : u ∈ U) (hul : u ∉ Sl) : upPt (upPt b c) u ≤ ceilPt b U Sl := by
  intro x
  refine Bool.le_iff_imp.mpr fun h => ?_
  by_cases hxu : x = u
  · subst hxu; simp [ceilPt, hu, hul]
  · rw [upPt, Function.update_of_ne hxu] at h
    exact (Bool.le_iff_imp.mp (upPt_le_ceilPt hc hcl x)) h

/-- Facts of a real merge set element. -/
theorem mergeSet_facts (gates : List Gate) {R : Finset (Fin n)} {z : Fin n → Bool} {x : ℕ}
    (hx : x ∈ mergeSet gates R z) :
    val gates z x = false ∧ ∃ u ∈ R, ∃ v ∈ R, u ≠ v ∧ val gates (upPt z u) x = true ∧
      val gates (upPt z v) x = true := by
  classical
  have h := mergeSet_subset_DT gates R z hx
  rw [DT, Finset.mem_filter] at h
  obtain ⟨-, hz, u, v, huv, hu, hv, h1, h2⟩ := h
  exact ⟨hz, u, hu, v, hv, huv, h1, h2⟩

theorem eq_of_inter {A B : Finset (Fin n)} (h : (A ∩ B).card ≤ 1) {u v : Fin n} (huA : u ∈ A)
    (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B) : u = v :=
  Finset.card_le_one.mp h u (Finset.mem_inter.mpr ⟨huA, huB⟩) v (Finset.mem_inter.mpr ⟨hvA, hvB⟩)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp hg hU hN in
/-- **Monotone comparison through the lift**: `y ≤ Y` and `ν y ≤ ν Y` ⇒ every real wire is smaller at
`y`. -/
theorem val_le_of_nu (x : ℕ) {y Y : Fin n → Bool} (hyY : y ≤ Y)
    (hnu : val gates y (n + p) ≤ val gates Y (n + p)) : val gates y x ≤ val gates Y x := by
  rw [val_lift (n := n) gates p hp y x, val_lift (n := n) gates p hp Y x]
  exact val_le_of_le _ (monoList_lift (n := n) gates p hp hg hU hN).andOr (ext_le_of_le hyY hnu) _

include hp hg hU hN in
/-- A wire `0` at `Y` is `0` at every `y ≤ Y` with `ν y ≤ ν Y`. -/
theorem low_of_below (x : ℕ) {y Y : Fin n → Bool} (hyY : y ≤ Y)
    (hnu : val gates Y (n + p) = false → val gates y (n + p) = false) (hY : val gates Y x = false) :
    val gates y x = false := by
  have hle : val gates y (n + p) ≤ val gates Y (n + p) := by
    cases hY' : val gates Y (n + p)
    · rw [hnu hY']
    · exact Bool.le_true _
  have h := val_le_of_nu gates p hp hg hU hN x hyY hle
  rw [hY] at h
  cases hv : val gates y x
  · rfl
  · rw [hv] at h; exact absurd h (by decide)

/-- **Condition `C(b)`** for one set `Sl` of the triple: `h(X_l) = 0` or `h(b + e_u) = 1` for every
`u ∈ U \ S_l` (in terms of the NOT gate). -/
def CondB (b : Fin n → Bool) (U Sl : Finset (Fin n)) : Prop :=
  val gates (ceilPt b U Sl) (n + p) = true ∨ ∀ u ∈ U, u ∉ Sl → val gates (upPt b u) (n + p) = false

include hp hg hU hN in
/-- **A base merge is never low at another ceiling.** -/
theorem notLow_base {b : Fin n → Bool} {U A C : Finset (Fin n)} (hAU : A ⊆ U)
    (hAC : (A ∩ C).card ≤ 1) (hcond : CondB gates p b U C) {x : ℕ} (hx : x ∈ mergeSet gates A b)
    (hlow : val gates (ceilPt b U C) x = false) : False := by
  obtain ⟨-, u, hu, v, hv, huv, h1, h2⟩ := mergeSet_facts gates hx
  have key : ∀ w ∈ A, val gates (upPt b w) x = true → w ∈ C := by
    intro w hw hwx
    by_contra hwC
    have := low_of_below gates p hp hg hU hN x (upPt_le_ceilPt (hAU hw) hwC) (fun h0 => by
      rcases hcond with h | h
      · rw [h0] at h; exact absurd h (by decide)
      · exact h w (hAU hw) hwC) hlow
    rw [this] at hwx; exact absurd hwx (by decide)
  exact huv (eq_of_inter hAC hu (key u hu h1) hv (key v hv h2))

include hp hg hU hN in
/-- **Triangle step.** If `γ` is low at the ceiling of `E` and every merge set of `A` meets
`{γ, γ'}`, then `γ'` is `1` at `b + e_c` (`c ∈ U`) only for `c ∈ A ∪ E`. -/
theorem triangle {b : Fin n → Bool} {U A E : Finset (Fin n)} (hb : ∀ v ∈ U, b v = false)
    (hAU : A ⊆ U) (hAE : (A ∩ E).card ≤ 1) (hcondE : CondB gates p b U E) {γ γ' : ℕ}
    (hγE : val gates (ceilPt b U E) γ = false)
    (hmA : ∀ z : Fin n → Bool, (∀ v ∈ A, z v = false) →
      ∃ x, (x = γ ∨ x = γ') ∧ x ∈ mergeSet gates A z)
    {c : Fin n} (hcU : c ∈ U) (hc : val gates (upPt b c) γ' = true) : c ∈ A ∨ c ∈ E := by
  by_contra hcon
  obtain ⟨hcA, hcE⟩ := not_or.mp hcon
  have hz : ∀ v ∈ A, upPt b c v = false := by
    intro v hv
    have hvc : v ≠ c := fun h => hcA (h ▸ hv)
    rw [upPt, Function.update_of_ne hvc]; exact hb v (hAU hv)
  obtain ⟨x, hxK, hxM⟩ := hmA _ hz
  have hx0 := (mergeSet_facts gates hxM).1
  have hxγ : x = γ := by
    rcases hxK with h | h
    · exact h
    · subst h; rw [hc] at hx0; exact absurd hx0 (by decide)
  subst hxγ
  obtain ⟨-, u, hu, v, hv, huv, h1, h2⟩ := mergeSet_facts gates hxM
  have key : ∀ w ∈ A, val gates (upPt (upPt b c) w) x = true → w ∈ E := by
    intro w hw hwx
    by_contra hwE
    have := low_of_below gates p hp hg hU hN x (upPt2_le_ceilPt hcU hcE (hAU hw) hwE) (fun h0 => by
      rcases hcondE with h | h
      · rw [h0] at h; exact absurd h (by decide)
      · exact not_false_of_le gates p hp hg hU hN (le_upPt _ w) (h c hcU hcE)) hγE
    rw [this] at hwx; exact absurd hwx (by decide)
  exact huv (eq_of_inter hAE hu (key u hu h1) hv (key v hv h2))

/-- **One run of the odd-cycle step.** A merge gate `n + k` of `L` at `b` whose trace lies in
`A ∪ E` (`|L ∩ A|, |L ∩ E| ≤ 1`), with a cover `(a₀, b₀)`: the two trace points, one in `A` and one in
`E`, take different values on `a₀`. -/
theorem run_split {L A E : Finset (Fin n)} (hLA : (L ∩ A).card ≤ 1) (hLE : (L ∩ E).card ≤ 1)
    {b : Fin n → Bool} {k : ℕ} (hk : n + k ∈ mergeSet gates L b)
    (htr : ∀ c ∈ L, val gates (upPt b c) (n + k) = true → c ∈ A ∨ c ∈ E) (a₀ b₀ : ℕ)
    (hcov : ∀ u : Fin n, val gates (upPt b u) (n + k) = true →
      (a₀ < n + k ∧ val gates b a₀ = false ∧ val gates (upPt b u) a₀ = true) ∨
      (b₀ < n + k ∧ val gates b b₀ = false ∧ val gates (upPt b u) b₀ = true)) :
    ∃ x ∈ L, x ∈ A ∧ ∃ y ∈ L, y ∈ E ∧ val gates (upPt b x) a₀ ≠ val gates (upPt b y) a₀ := by
  classical
  obtain ⟨j, hj, hjk, hmg⟩ := (runMT_mem b (upPt b) L gates gates.length (n + k)).mp hk
  have hjk' : j = k := by omega
  subst hjk'
  set l := runLT b (upPt b) L gates j with hl
  have hinv := runLT_inv b (upPt b) L gates (fun u _ c h1 h2 => upPt_hT b u c h1 h2) j
  have hmem : ∀ d, d ∈ trRT (upPt b) L gates (n + j) ↔ d ∈ L ∧ val gates (upPt b d) (n + j) = true :=
    fun d => Finset.mem_filter
  -- not every trace point has the `a₀`-condition, nor every one the `b₀`-condition
  have hone : ∀ w : ℕ, w < n + j → val gates b w = false →
      ¬ ∀ d ∈ trRT (upPt b) L gates (n + j), val gates (upPt b d) w = true := by
    intro w hw hwz hall
    have : ((trRT (upPt b) L gates (n + j)).image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hy
      exact hinv w hw hwz d ((hmem d).mp hd).1 d' ((hmem d').mp hd').1 (hall d hd) (hall d' hd')
    have := hmg.2
    omega
  -- a trace point without the `a₀`-condition, and one without the `b₀`-condition
  have hA : ∃ d ∈ trRT (upPt b) L gates (n + j),
      ¬ (a₀ < n + j ∧ val gates b a₀ = false ∧ val gates (upPt b d) a₀ = true) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨d0, hd0⟩ : (trRT (upPt b) L gates (n + j)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have := hmg.2
      rw [he] at this
      simp at this
    obtain ⟨h1, h2, -⟩ := hcon d0 hd0
    exact hone a₀ h1 h2 fun d hd => (hcon d hd).2.2
  have hB : ∃ d ∈ trRT (upPt b) L gates (n + j),
      ¬ (b₀ < n + j ∧ val gates b b₀ = false ∧ val gates (upPt b d) b₀ = true) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨d0, hd0⟩ : (trRT (upPt b) L gates (n + j)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have := hmg.2
      rw [he] at this
      simp at this
    obtain ⟨h1, h2, -⟩ := hcon d0 hd0
    exact hone b₀ h1 h2 fun d hd => (hcon d hd).2.2
  obtain ⟨d1, hd1, hna⟩ := hA
  obtain ⟨d2, hd2, hnb⟩ := hB
  obtain ⟨hd1L, hd1v⟩ := (hmem d1).mp hd1
  obtain ⟨hd2L, hd2v⟩ := (hmem d2).mp hd2
  have ha2 := (hcov d2 hd2v).resolve_right hnb
  have hv1 : val gates (upPt b d1) a₀ = false := by
    cases h : val gates (upPt b d1) a₀
    · rfl
    · exact absurd ⟨ha2.1, ha2.2.1, h⟩ hna
  have hdiff : val gates (upPt b d1) a₀ ≠ val gates (upPt b d2) a₀ := by
    rw [hv1, ha2.2.2]; decide
  have hd12 : d1 ≠ d2 := fun h => hdiff (h ▸ rfl)
  rcases htr d1 hd1L hd1v with h1A | h1E <;> rcases htr d2 hd2L hd2v with h2A | h2E
  · exact absurd (eq_of_inter hLA hd1L h1A hd2L h2A) hd12
  · exact ⟨d1, hd1L, h1A, d2, hd2L, h2E, hdiff⟩
  · exact ⟨d2, hd2L, h2A, d1, hd1L, h1E, fun h => hdiff h.symm⟩
  · exact absurd (eq_of_inter hLE hd1L h1E hd2L h2E) hd12

/-- The pigeonhole step on the six gates. -/
theorem pigeon_two {g g' Gi Gj Gk Hi Hj Hk : ℕ} (hGi : Gi = g ∨ Gi = g') (hGj : Gj = g ∨ Gj = g')
    (hGk : Gk = g ∨ Gk = g') (hHi : Hi = g ∨ Hi = g') (hHj : Hj = g ∨ Hj = g')
    (hHk : Hk = g ∨ Hk = g') (h1 : Hi ≠ Gj) (h2 : Hi ≠ Gk) (h3 : Hj ≠ Gi) (h4 : Hj ≠ Gk)
    (h5 : Hk ≠ Gi) (h6 : Hk ≠ Gj) :
    Gj = Gi ∧ Gk = Gi ∧ Hj = Hi ∧ Hk = Hi ∧ ∀ x, x = g ∨ x = g' → x = Gi ∨ x = Hi := by
  refine ⟨by omega, by omega, by omega, by omega, fun x hx => by omega⟩

include hp hg hU hN in
/-- **Theorem 2G-LIFT, core** (front A1 §9): under `C(b)` for a triple of distinct sets, the three sets
cannot each meet `{g, g'}` in every merge set. -/
theorem twoGate_triple (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (b : Fin n → Bool)
    (hb : ∀ v ∈ S i ∪ S j ∪ S k, b v = false)
    (hC : ∀ l, l = i ∨ l = j ∨ l = k → CondB gates p b (S i ∪ S j ∪ S k) (S l)) (g g' : ℕ)
    (hm : ∀ l, l = i ∨ l = j ∨ l = k → ∀ z : Fin n → Bool, (∀ v ∈ S l, z v = false) →
      ∃ x, (x = g ∨ x = g') ∧ x ∈ mergeSet gates (S l) z) : False := by
  classical
  set U := S i ∪ S j ∪ S k with hUdef
  have hsub : ∀ l, l = i ∨ l = j ∨ l = k → S l ⊆ U := by
    rintro l (rfl | rfl | rfl) x hx <;> simp [hUdef, hx]
  have hTi : i = i ∨ i = j ∨ i = k := Or.inl rfl
  have hTj : j = i ∨ j = j ∨ j = k := Or.inr (Or.inl rfl)
  have hTk : k = i ∨ k = j ∨ k = k := Or.inr (Or.inr rfl)
  -- ceilings and bases
  have hceil : ∀ l, l = i ∨ l = j ∨ l = k → ∃ G, (G = g ∨ G = g') ∧
      G ∈ mergeSet gates (S l) (ceilPt b U (S l)) := fun l hl =>
    hm l hl _ (ceilPt_zero hb (hsub l hl))
  have hbase : ∀ l, l = i ∨ l = j ∨ l = k → ∃ H, (H = g ∨ H = g') ∧ H ∈ mergeSet gates (S l) b :=
    fun l hl => hm l hl b fun v hv => hb v (hsub l hl hv)
  obtain ⟨Gi, hGi, hGiM⟩ := hceil i hTi
  obtain ⟨Gj, hGj, hGjM⟩ := hceil j hTj
  obtain ⟨Gk, hGk, hGkM⟩ := hceil k hTk
  obtain ⟨Hi, hHi, hHiM⟩ := hbase i hTi
  obtain ⟨Hj, hHj, hHjM⟩ := hbase j hTj
  obtain ⟨Hk, hHk, hHkM⟩ := hbase k hTk
  have lowG : ∀ {l G}, G ∈ mergeSet gates (S l) (ceilPt b U (S l)) →
      val gates (ceilPt b U (S l)) G = false := fun h => (mergeSet_facts gates h).1
  -- a base merge of `a` is not low at the ceiling of `c ≠ a`
  have hne : ∀ {a c : Fin m} {H G : ℕ}, (a = i ∨ a = j ∨ a = k) → (c = i ∨ c = j ∨ c = k) → a ≠ c →
      H ∈ mergeSet gates (S a) b → G ∈ mergeSet gates (S c) (ceilPt b U (S c)) → H ≠ G := by
    intro a c H G ha hc hac hH hG hHG
    subst hHG
    exact notLow_base gates p hp hg hU hN (hsub a ha) (hS a c hac) (hC c hc) hH (lowG hG)
  obtain ⟨hGj', hGk', hHj', hHk', hK⟩ := pigeon_two hGi hGj hGk hHi hHj hHk
    (hne hTi hTj hij hHiM hGjM) (hne hTi hTk hik hHiM hGkM) (hne hTj hTi hij.symm hHjM hGiM)
    (hne hTj hTk hjk hHjM hGkM) (hne hTk hTi hik.symm hHkM hGiM) (hne hTk hTj hjk.symm hHkM hGjM)
  rw [hGj'] at hGjM
  rw [hGk'] at hGkM
  rw [hHj'] at hHjM
  rw [hHk'] at hHkM
  -- `γ = Gi` is low at all three ceilings, `γ' = Hi` merges for all three sets at `b`
  have hmγ : ∀ l, l = i ∨ l = j ∨ l = k → ∀ z : Fin n → Bool, (∀ v ∈ S l, z v = false) →
      ∃ x, (x = Gi ∨ x = Hi) ∧ x ∈ mergeSet gates (S l) z := by
    intro l hl z hz
    obtain ⟨x, hx, hxM⟩ := hm l hl z hz
    exact ⟨x, hK x hx, hxM⟩
  -- the merge gate `γ'` and one cover of it, valid for all three runs
  obtain ⟨hHi0, u0, hu0, v0, hv0, huv0, hu0t, hv0t⟩ := mergeSet_facts gates hHiM
  obtain ⟨kk, -, hkk, -⟩ := (runMT_mem b (upPt b) (S i) gates gates.length Hi).mp hHiM
  subst hkk
  obtain ⟨a₀, b₀, hcov⟩ := (mr_coverT b (upPt b) Finset.univ gates
    (goodT_upPt gates hg hU b Finset.univ) kk hHi0).resolve_left fun h =>
    huv0 (h u0 (Finset.mem_univ _) v0 (Finset.mem_univ _) hu0t hv0t)
  -- the three runs
  have tri : ∀ {l a e : Fin m}, (l = i ∨ l = j ∨ l = k) → (a = i ∨ a = j ∨ a = k) →
      (e = i ∨ e = j ∨ e = k) → a ≠ e →
      ∀ c ∈ S l, val gates (upPt b c) (n + kk) = true → c ∈ S a ∨ c ∈ S e := by
    intro l a e hl ha he hae c hc hcv
    exact triangle gates p hp hg hU hN hb (hsub a ha) (hS a e hae) (hC e he)
      (show val gates (ceilPt b U (S e)) Gi = false from by
        rcases he with rfl | rfl | rfl
        · exact lowG hGiM
        · exact lowG hGjM
        · exact lowG hGkM)
      (hmγ a ha) (hsub l hl hc) hcv
  obtain ⟨x1, hx1i, hx1j, y1, hy1i, hy1k, h1⟩ := run_split gates (hS i j hij) (hS i k hik) hHiM
    (tri hTi hTj hTk hjk) a₀ b₀ hcov
  obtain ⟨x2, hx2j, hx2i, y2, hy2j, hy2k, h2⟩ := run_split gates (hS j i hij.symm) (hS j k hjk) hHjM
    (tri hTj hTi hTk hik) a₀ b₀ hcov
  obtain ⟨x3, hx3k, hx3i, y3, hy3k, hy3j, h3⟩ := run_split gates (hS k i hik.symm) (hS k j hjk.symm) hHkM
    (tri hTk hTi hTj hij) a₀ b₀ hcov
  have e12 : x1 = x2 := eq_of_inter (hS i j hij) hx1i hx1j hx2i hx2j
  have e13 : y1 = x3 := eq_of_inter (hS i k hik) hy1i hy1k hx3i hx3k
  have e23 : y2 = y3 := eq_of_inter (hS j k hjk) hy2j hy2k hy3j hy3k
  subst e12 e13 e23
  revert h1 h2 h3
  cases val gates (upPt b x1) a₀ <;> cases val gates (upPt b y1) a₀ <;>
    cases val gates (upPt b y2) a₀ <;> decide

/-- `m_w = min_{z zero point of S_w} |M_z(w) ∩ {g, g'}|` (real merge sets). -/
noncomputable def minHit (S : Fin m → Finset (Fin n)) (w : Fin m) (g g' : ℕ) : ℕ :=
  (zeroPts (S w)).inf' (zeroPts_nonempty (S w)) fun z => (mergeSet gates (S w) z ∩ {g, g'}).card

theorem minHit_le_two (S : Fin m → Finset (Fin n)) (w : Fin m) (g g' : ℕ) :
    minHit gates S w g g' ≤ 2 := by
  obtain ⟨z, hz⟩ := zeroPts_nonempty (S w)
  refine (Finset.inf'_le _ hz).trans ?_
  exact (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_le_two)

theorem one_le_minHit {S : Fin m → Finset (Fin n)} {w : Fin m} {g g' : ℕ}
    (h : 1 ≤ minHit gates S w g g') (z : Fin n → Bool) (hz : ∀ v ∈ S w, z v = false) :
    ∃ x, (x = g ∨ x = g') ∧ x ∈ mergeSet gates (S w) z := by
  have h1 := h.trans (Finset.inf'_le _ (mem_zeroPts.mpr hz))
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < _ from h1)
  obtain ⟨hxM, hxK⟩ := Finset.mem_inter.mp hx
  rcases Finset.mem_insert.mp hxK with rfl | hx'
  · exact ⟨_, Or.inl rfl, hxM⟩
  · exact ⟨x, Or.inr (Finset.mem_singleton.mp hx'), hxM⟩

include hp hg hU hN in
/-- **Theorem 2G-LIFT** (front A1 §§8–9, refereed 12:31): `∑_w m_w ≤ 2` for every two gates, if every
triple of distinct sets satisfies `C(b)` for some `b`. -/
theorem twoGate_lift (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hCall : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k → ∃ b : Fin n → Bool,
      (∀ v ∈ S i ∪ S j ∪ S k, b v = false) ∧
        ∀ l, l = i ∨ l = j ∨ l = k → CondB gates p b (S i ∪ S j ∪ S k) (S l))
    (g g' : ℕ) : ∑ w, minHit gates S w g g' ≤ 2 := by
  classical
  by_cases hA : ∃ w, 2 ≤ minHit gates S w g g'
  · -- case A: both gates are universal merges of `w`; every other set has `m_v = 0`
    obtain ⟨w, hw⟩ := hA
    have hboth : ∀ z ∈ zeroPts (S w), g ∈ mergeSet gates (S w) z ∧ g' ∈ mergeSet gates (S w) z := by
      intro z hz
      have h2 := hw.trans (Finset.inf'_le _ hz)
      have hK2 : ({g, g'} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      have hsub : mergeSet gates (S w) z ∩ {g, g'} = {g, g'} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact ⟨Finset.mem_of_mem_inter_left (hsub ▸ Finset.mem_insert_self g {g'}),
        Finset.mem_of_mem_inter_left (hsub ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self g'))⟩
    have huniv : ∀ x, (x = g ∨ x = g') → x ∈ univMergeSet S gates w := by
      rintro x (rfl | rfl)
      · exact (mem_univMergeSet S gates).mpr fun z hz => (hboth z hz).1
      · exact (mem_univMergeSet S gates).mpr fun z hz => (hboth z hz).2
    have hzero : ∀ v, v ≠ w → minHit gates S v g g' = 0 := by
      intro v hvw
      have hz : ∀ x ∈ S v ∪ S w, Zof (S v ∪ S w) x = false := fun x hx => by simp [Zof, hx]
      have hdis := disjoint_univMergeSet S gates hS hvw _ hz
      refine Nat.le_zero.mp ((Finset.inf'_le _ (mem_zeroPts.mpr fun x hx =>
        hz x (Finset.mem_union_left _ hx))).trans (Nat.le_zero.mpr ?_))
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxM, hxK⟩ := Finset.mem_inter.mp hx
      have hxK' : x = g ∨ x = g' := by
        rcases Finset.mem_insert.mp hxK with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.mp h)
      exact Finset.disjoint_left.mp hdis hxM (huniv x hxK')
    rw [Finset.sum_eq_single w (fun v _ hv => hzero v hv) (by simp)]
    exact minHit_le_two gates S w g g'
  · -- case B: every `m_w ≤ 1`; at most two sets have `m_w = 1`
    push Not at hA
    have hcard : (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card ≤ 2 := by
      by_contra hc
      obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp
        (show 2 < (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card by omega)
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      obtain ⟨b, hb, hC⟩ := hCall i j k hij hik hjk
      exact twoGate_triple gates p hp hg hU hN S hS hij hik hjk b hb hC g g' fun l hl z hz => by
        rcases hl with rfl | rfl | rfl
        · exact one_le_minHit gates hi' z hz
        · exact one_le_minHit gates hj' z hz
        · exact one_le_minHit gates hk' z hz
    calc ∑ w, minHit gates S w g g'
        ≤ ∑ w, (if 1 ≤ minHit gates S w g g' then 1 else 0) := Finset.sum_le_sum fun w _ => by
          have := hA w
          split_ifs with h <;> omega
      _ = (Finset.univ.filter fun w => 1 ≤ minHit gates S w g g').card := by
          rw [Finset.sum_boole]; simp
      _ ≤ 2 := hcard

/-! ## Special cases of `C(b)` (front §§8–9) -/

include hp hg hU hN in
/-- `h(b) = 1` (the NOT gate is `0` at `b`) gives `C(b)` for every set (`h(b + e_u) = 1` by monotonicity). -/
theorem condB_of_hb {b : Fin n → Bool} (U Sl : Finset (Fin n)) (hb1 : val gates b (n + p) = false) :
    CondB gates p b U Sl :=
  Or.inr fun u _ _ => not_false_of_le gates p hp hg hU hN (le_upPt b u) hb1

include hp hg hU hN in
/-- **2G-LIFT, case `h(¬(S_i ∪ S_j ∪ S_k)) = 1`** for every triple (base point `b = ¬∪S`). -/
theorem twoGate_of_hY (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hY : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k → val gates (Zof (S i ∪ S j ∪ S k)) (n + p) = false)
    (g g' : ℕ) : ∑ w, minHit gates S w g g' ≤ 2 :=
  twoGate_lift gates p hp hg hU hN S hS (fun i j k hij hik hjk =>
    ⟨Zof (S i ∪ S j ∪ S k), fun v hv => by simp only [Zof, hv, not_true_eq_false, decide_false],
      fun _ _ => condB_of_hb gates p hp hg hU hN _ _ (hY i j k hij hik hjk)⟩) g g'

include hp hg hU hN in
/-- **2G-LIFT, all points heavy** (`h(e_u) = 1` for every point of every set; base point `b = 0`). -/
theorem twoGate_of_heavy (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hheavy : ∀ w, ∀ u ∈ S w, val gates (upPt (fun _ => false) u) (n + p) = false) (g g' : ℕ) :
    ∑ w, minHit gates S w g g' ≤ 2 :=
  twoGate_lift gates p hp hg hU hN S hS (fun i j k _ _ _ =>
    ⟨fun _ => false, fun _ _ => rfl, fun _ _ => Or.inr fun u hu _ => by
      simp only [Finset.mem_union] at hu
      rcases hu with (hu | hu) | hu
      · exact hheavy i u hu
      · exact hheavy j u hu
      · exact hheavy k u hu⟩) g g'

include hp hg hU hN in
/-- **2G-LIFT, all sets type B relative to every triple** (`h((S_i ∪ S_j ∪ S_k) \ S_l) = 0`, i.e. the NOT
gate is `1` there; base point `b = 0`). -/
theorem twoGate_of_typeB (S : Fin m → Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hB : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k → ∀ l, l = i ∨ l = j ∨ l = k →
      val gates (ceilPt (fun _ => false) (S i ∪ S j ∪ S k) (S l)) (n + p) = true)
    (g g' : ℕ) : ∑ w, minHit gates S w g g' ≤ 2 :=
  twoGate_lift gates p hp hg hU hN S hS (fun i j k hij hik hjk =>
    ⟨fun _ => false, fun _ _ => rfl, fun l hl => Or.inl (hB i j k hij hik hjk l hl)⟩) g g'

end TwoGate

end PEqualNP.Outside.L_meta_951_aux

end TwoGateLift

section OneNotIff

/-!
# The literal statement of `L_meta_951` is equivalent to `OneNotBound`

`LMeta951Statement` is the type of `PEqualNP.Outside.L_meta_951`, copied verbatim from Final.lean
(`example : LMeta951Statement := PEqualNP.Outside.L_meta_951` typechecks; it is not included here,
so that nothing in this file depends on `no_minCE`).

The two statements differ in two places.
* Evaluation: `Circuit.eval ⟨gates, out w⟩ (List.ofFn x)` against `val gates x (out w)`; these are
  equal by unfolding (`circuit_eval_eq_val`).
* At most one NOT: `∃ ι : Fin 1 → Fin gates.length, ...` against `AtMostOneNot gates`. For
  `gates ≠ []` they are equivalent (`ι_iff_atMostOneNot`). For `gates = []` there is no
  `ι : Fin 1 → Fin 0`, so the literal statement says nothing about the empty circuit, while
  `AtMostOneNot []` holds. `OneNotBound` is still true there: an empty circuit computes no
  `OR(S w)` with `2 ≤ |S w|` (`no_output_of_nil`), so `m = 0` and the sum is `0`
  (`oneNotBound_nil`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The statement (type) of `PEqualNP.Outside.L_meta_951`, verbatim. -/
def LMeta951Statement : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length

/-- `Circuit.eval` on `List.ofFn x` is `val`. -/
theorem circuit_eval_eq_val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (o : ℕ) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = val gates x o := rfl

/-- The converse of `hU_of_ι`, for a nonempty circuit. -/
theorem ι_of_atMostOneNot {gates : List Gate} (hne : gates ≠ []) (hU : AtMostOneNot gates) :
    ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
  have hpos : 0 < gates.length := List.length_pos_iff.mpr hne
  by_cases h : ∃ i : Fin gates.length, (gates.get i).op = GateOp.not
  · obtain ⟨i0, h0⟩ := h
    refine ⟨fun _ => i0, fun i hi => ⟨0, ?_⟩⟩
    exact Fin.ext (hU i0 i i0.2 i.2 (by simpa using h0) (by simpa using hi))
  · exact ⟨fun _ => ⟨0, hpos⟩, fun i hi => absurd ⟨i, hi⟩ h⟩

/-- For a nonempty circuit, the `ι` encoding is `AtMostOneNot`. -/
theorem ι_iff_atMostOneNot {gates : List Gate} (hne : gates ≠ []) :
    (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i) ↔ AtMostOneNot gates :=
  ⟨hU_of_ι, ι_of_atMostOneNot hne⟩

/-- For the empty circuit the `ι` encoding is false (`Fin 1 → Fin 0` is empty)... -/
theorem not_ι_nil : ¬ ∃ ι : Fin 1 → Fin ([] : List Gate).length, ∀ i : Fin ([] : List Gate).length,
    (([] : List Gate).get i).op = GateOp.not → ∃ j : Fin 1, ι j = i :=
  fun ⟨ι, _⟩ => (ι 0).elim0

/-- ... while `AtMostOneNot []` is true. -/
theorem atMostOneNot_nil : AtMostOneNot ([] : List Gate) :=
  fun _ _ h1 => absurd h1 (by simp)

/-- The empty circuit computes no `OR(T)` with `2 ≤ |T|`, at any output wire `o` (an input, or out
of range, which reads `false`). -/
theorem no_output_of_nil {n : ℕ} (T : Finset (Fin n)) (hT : 2 ≤ T.card) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val [] x o = decide (∃ v ∈ T, x v = true)) : False := by
  by_cases h : o < n
  · obtain ⟨v, hv, hne⟩ : ∃ v ∈ T, v ≠ ⟨o, h⟩ := by
      by_contra hc
      push Not at hc
      have : T ⊆ {⟨o, h⟩} := fun v hv => Finset.mem_singleton.mpr (hc v hv)
      have := Finset.card_le_card this
      simp at this
      omega
    have := hev (fun u => decide (u = v))
    simp only [val_nil, h, ↓reduceDIte] at this
    have h1 : decide ((⟨o, h⟩ : Fin n) = v) = false := by simpa using fun e => hne e.symm
    rw [h1] at this
    have h2 : decide (∃ u ∈ T, decide (u = v) = true) = true := by simpa using hv
    rw [h2] at this
    exact Bool.false_ne_true this
  · obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    have := hev (fun _ => true)
    simp only [val_nil, h, ↓reduceDIte] at this
    exact Bool.false_ne_true (this.trans (decide_eq_true ⟨v, hv, trivial⟩))

/-- `OneNotBound` for the empty circuit: there is no output, so the sum is `0`. -/
theorem oneNotBound_nil {n m : ℕ} (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val [] x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ ([] : List Gate).length := by
  have : IsEmpty (Fin m) := ⟨fun w => no_output_of_nil (S w) (h2 w) (out w) (hev w)⟩
  simp

/-- The literal statement of `L_meta_951` implies `OneNotBound`. -/
theorem oneNotBound_of_lMeta951Statement (H : LMeta951Statement) : OneNotBound := by
  intro n m S h2 hS gates out hg hU hev
  by_cases hne : gates = []
  · subst hne
    exact oneNotBound_nil S h2 out hev
  · exact H n m S h2 hS gates out hg (ι_of_atMostOneNot hne hU) hev

/-- `OneNotBound` implies the literal statement of `L_meta_951`. -/
theorem lMeta951Statement_of_oneNotBound (H : OneNotBound) : LMeta951Statement := by
  intro n m S h2 hS gates out hg hι hev
  exact H n m S h2 hS gates out hg (hU_of_ι hι) hev

/-- The literal statement of `L_meta_951` is equivalent to `OneNotBound`. -/
theorem L_meta_951_iff_oneNotBound : LMeta951Statement ↔ OneNotBound :=
  ⟨oneNotBound_of_lMeta951Statement, lMeta951Statement_of_oneNotBound⟩

/-- The literal statement is also equivalent to `LiftedBound`. -/
theorem L_meta_951_iff_liftedBound : LMeta951Statement ↔ LiftedBound :=
  L_meta_951_iff_oneNotBound.trans liftedBound_iff_oneNotBound.symm

end PEqualNP.Outside.L_meta_951_aux

end OneNotIff

section CanonD1

/-!
# CanonD1: lemma D at every I1 point (candidate "D1") — per-atom D proved, D1 REFUTED

Notation of `CanonOneNot.lean`. For a set `R = S_w` and a zero point `Z` of `w`, `K1Z gates p R Z`
is the world-1 class at `Z` (OR gates of the lift `0` at `(Z, 1)` and `1` at `(e_u, 1)` for two
`u ∈ R` or more); `K1Z gates p R (Zof R) = K1 gates p R`. For a set `R' = S_v` and an I0 choice
`m : Fin n → Finset (Fin n)` (`m u'` the minterm chosen for the atom `u' ∈ R'`), `K0of gates p R' m`
is the world-0 class with per-atom bases (OR gates `0` at `(top_v, 0)` and `1` at
`(m u' + e_u', 0)` for two `u' ∈ R'` or more); `K0of gates p R' (fun _ => m) = K0 gates p R' m`.

* `disjoint_K0of_K1` (**D at `top_w`, per-atom choices**): `K_0(v; (m_u')) ∩ K_1(w) = ∅` for
  `|S_v ∩ S_w| ≤ 1` once every `m_u' ∩ S_w = ∅`. (CanonOneNot's `disjoint_K0_K1` has one common `m`.)
* `disjoint_K0of_K1Z_of_le` (D's argument at an arbitrary `Z`): disjoint whenever of any two
  world-0 atoms of `v` one lies below `Z` (as a real point, `m u' ∪ {u'} ⊆ Z`).
* `atom0_not_le_Z`, `atom1_not_le_ext_false` (**where `Z ≠ top_w` breaks D**): if the NOT gate is
  `1` at `Z` (`h(Z) = 0`) and `0` at `m` (`h(m) = 1`), then NO world-0 atom `(m + e_u', 0)` lies
  below `(Z, 1)`; and no world-1 atom `(e_u, 1)` lies below any `(Z', 0)`. So neither orientation of
  `orClz_disjoint` applies to `K1Z(w; Z)` against `K0of(v; m)` once `|S_v| ≥ 2`
  (`D_hyp_fails`), for EVERY I1 point `Z`, including `Z = top_w` when `h(top_w) = 0`
  (there D is used against minterms avoiding `S_w`, which `top_w` contains: `h(top_w) = 1`).
* `D1Stmt` (the candidate as a `Prop`, over all correct one-NOT circuits) and `not_D1Stmt`:
  **D1 is false**. Counterexample on `n = 5`, `S_w = {0,1}`, `S_v = {2,3}`, `h = x_4`,
  `Z = top_w \ {4} = {2,3}`, `m_2 = m_3 = {4}`: the gate
  `g = (y ∧ x_0 ∨ x_4 ∧ x_2) ∨ (y ∧ x_1 ∨ x_4 ∧ x_3)` lies in both classes (also in both merge
  sets of `tools/kill_tests/canon.py`; `typeA.py` reports the collision).

Fully proved, no `sorry`.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CanonD1

variable {n : ℕ}

/-! ## The classes at an arbitrary zero point / with per-atom bases -/

/-- **`K_1(w; Z)`** (world 1 at the zero point `Z`), as real wires. -/
noncomputable def K1Z (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) (Z : Fin n → Bool) :
    Finset ℕ :=
  (orClz (lift n p gates) (ext Z true)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) {Fin.last n}))).image (realWire n p)

/-- **`K_0(v; (m_u'))`** (world 0, one base `m u'` per atom `u' ∈ R`), as real wires. -/
noncomputable def K0of (gates : List Gate) (p : ℕ) (R : Finset (Fin n))
    (m : Fin n → Finset (Fin n)) : Finset ℕ :=
  (orClz (lift n p gates) (ext (Zof R) false)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) (liftSet (m (enumF R t)))))).image
    (realWire n p)

theorem K1Z_top (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) :
    K1Z gates p R (Zof R) = K1 gates p R := rfl

theorem K0of_const (gates : List Gate) (p : ℕ) (R m : Finset (Fin n)) :
    K0of gates p R (fun _ => m) = K0 gates p R m := rfl

/-! ## Points -/

theorem d1_ext_le_ext {x z : Fin n → Bool} {b b' : Bool} (hxz : x ≤ z) (hb : b ≤ b') :
    ext x b ≤ ext z b' := by
  intro c
  induction c using Fin.lastCases with
  | last => rw [ext_last, ext_last]; exact hb
  | cast c => rw [ext_castSucc, ext_castSucc]; exact hxz c

theorem le_of_ext_le {x z : Fin n → Bool} {b b' : Bool} (h : ext x b ≤ ext z b') : x ≤ z := by
  intro c
  have := h (Fin.castSucc c)
  rwa [ext_castSucc, ext_castSucc] at this

theorem canonPt_mono {A B : Finset (Fin n)} (h : A ⊆ B) : canonPt A ≤ canonPt B := by
  intro c
  refine Bool.le_iff_imp.mpr fun hc => ?_
  exact canonPt_eq_true.mpr (h (canonPt_eq_true.mp hc))

/-- A world-0 atom `(M + e_u, 0)` lies below `(top_{R'}, 1)` if `u ∉ R'` and `M ∩ R' = ∅`. -/
theorem atom0_le_top (R' M : Finset (Fin n)) (u : Fin n) (hu : u ∉ R') (hM : Disjoint M R') :
    canonPt (insert (Fin.castSucc u) (liftSet M)) ≤ ext (Zof R') true := by
  rw [atom0_eq]
  refine d1_ext_le_ext (fun c => Bool.le_iff_imp.mpr fun hc => ?_) (by decide)
  have hc' := canonPt_eq_true.mp hc
  simp only [Zof, decide_eq_true_eq]
  rcases Finset.mem_insert.mp hc' with rfl | hc'
  · exact hu
  · exact Finset.disjoint_left.mp hM hc'

/-! ## D at `top_w` with per-atom choices -/

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **D, general zero point.** `K_0(v; (m_u')) ∩ K_1(w; Z) = ∅` whenever of any two distinct
`u, u' ∈ S_v` one has `m_u ∪ {u} ⊆ Z` (as points: `canonPt (insert u (m u)) ≤ Z`). -/
theorem disjoint_K0of_K1Z_of_le (R R' : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (Z : Fin n → Bool)
    (hle : ∀ u ∈ R, ∀ u' ∈ R, u ≠ u' →
      canonPt (insert u (m u)) ≤ Z ∨ canonPt (insert u' (m u')) ≤ Z) :
    Disjoint (K0of gates p R m) (K1Z gates p R' Z) := by
  classical
  rw [K0of, K1Z, Finset.disjoint_image (realWire_injective n p)]
  refine orClz_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _
    fun s t hst => ?_
  have hne : enumF R s ≠ enumF R t := fun h => hst (enumF_injective R h)
  rcases hle _ (enumF_mem R s) _ (enumF_mem R t) hne with h | h
  · left; rw [atom0_eq]; exact d1_ext_le_ext h (by decide)
  · right; rw [atom0_eq]; exact d1_ext_le_ext h (by decide)

include hg hU hN in
/-- **D at `top_w`, per-atom I0 choices.** `K_0(v; (m_u')) ∩ K_1(w) = ∅` for `|S_v ∩ S_w| ≤ 1`
once every `m_u'` (`u' ∈ S_v`) avoids `S_w`. -/
theorem disjoint_K0of_K1 (R R' : Finset (Fin n)) (m : Fin n → Finset (Fin n))
    (hRR : (R ∩ R').card ≤ 1) (hm : ∀ u ∈ R, Disjoint (m u) R') :
    Disjoint (K0of gates p R m) (K1 gates p R') := by
  classical
  rw [K0of, K1, Finset.disjoint_image (realWire_injective n p)]
  refine orClz_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _
    fun s t hst => ?_
  have hne : enumF R s ≠ enumF R t := fun h => hst (enumF_injective R h)
  by_cases hs : enumF R s ∈ R'
  · right
    refine atom0_le_top R' _ _ (fun ht => ?_) (hm _ (enumF_mem R t))
    have hsub : ({enumF R s, enumF R t} : Finset (Fin n)) ⊆ R ∩ R' := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact Finset.mem_inter.mpr ⟨enumF_mem R s, hs⟩
      · rw [Finset.mem_singleton.mp hc]
        exact Finset.mem_inter.mpr ⟨enumF_mem R t, ht⟩
    have h2 := Finset.card_pair hne
    have h3 := Finset.card_le_card hsub
    omega
  · exact Or.inl (atom0_le_top R' _ _ hs (hm _ (enumF_mem R s)))

/-! ## Where `Z ≠ top_w` breaks D -/

include hg hU hN in
/-- **The obstruction.** If the NOT gate is `1` at `Z` (`h(Z) = 0`) and `0` at `canonPt M`
(`h(M) = 1`), then no world-0 atom `(M + e_u, 0)` lies below `(Z, 1)`. -/
theorem atom0_not_le_Z (Z : Fin n → Bool) (M : Finset (Fin n)) (u : Fin n)
    (hZ : val gates Z (n + p) = true) (hM : val gates (canonPt M) (n + p) = false) :
    ¬ canonPt (insert (Fin.castSucc u) (liftSet M)) ≤ ext Z true := by
  intro hle
  rw [atom0_eq] at hle
  have h1 : canonPt M ≤ Z :=
    (canonPt_mono (Finset.subset_insert u M)).trans (le_of_ext_le hle)
  have := not_false_of_le gates p hp hg hU hN h1 hM
  rw [hZ] at this
  exact absurd this (by decide)

/-- No world-1 atom `(A, 1)` lies below a world-0 point `(Z', 0)`. -/
theorem atom1_not_le_ext_false (A : Finset (Fin (n + 1))) (Z' : Fin n → Bool) :
    ¬ canonPt (insert (Fin.last n) A) ≤ ext Z' false := by
  intro hle
  have := hle (Fin.last n)
  rw [ext_last, canonPt_eq_true.mpr (Finset.mem_insert_self _ _)] at this
  exact absurd this (show ¬ (true ≤ false) from fun h => Bool.noConfusion (h rfl))

include hg hU hN in
/-- **D's hypothesis fails at every I1 point.** If the NOT gate is `1` at `Z` and `0` at every
chosen `m u'`, and `S_v` has two distinct points, the hypothesis of `orClz_disjoint` (first system
`K_0(v; m)`, second zero point `(Z, 1)`) is false. -/
theorem D_hyp_fails (R : Finset (Fin n)) (m : Fin n → Finset (Fin n)) (Z : Fin n → Bool)
    (hZ : val gates Z (n + p) = true)
    (hm : ∀ u ∈ R, val gates (canonPt (m u)) (n + p) = false) (h2 : 1 < R.card) :
    ¬ ∀ s t : Fin R.card, s ≠ t →
      canonPt (insert (Fin.castSucc (enumF R s)) (liftSet (m (enumF R s)))) ≤ ext Z true ∨
      canonPt (insert (Fin.castSucc (enumF R t)) (liftSet (m (enumF R t)))) ≤ ext Z true := by
  intro h
  have hne : (⟨0, by omega⟩ : Fin R.card) ≠ ⟨1, h2⟩ := by simp [Fin.ext_iff]
  rcases h _ _ hne with h' | h'
  · exact atom0_not_le_Z gates p hp hg hU hN Z _ _ hZ (hm _ (enumF_mem R _)) h'
  · exact atom0_not_le_Z gates p hp hg hU hN Z _ _ hZ (hm _ (enumF_mem R _)) h'

end CanonD1

/-! ## D1 as stated is false -/

/-- **Candidate D1** over all correct one-NOT circuits: `w ≠ v` given by `R = S_w`, `R' = S_v`
(`|S_w ∩ S_v| ≤ 1`, outputs `o`, `o'` computing `OR_R`, `OR_R'`); `Z` an I1 point of `w` (false on
`R`, `h(Z) = 0`, maximal); `m` an I0 choice of `v` (each `m u'`, `u' ∈ R'`, a minterm of `h` with
`m u' ∩ R' ⊆ {u'}`) with every `m u' ∩ R = ∅`. Then `K_1(w; Z) ∩ K_0(v; m) = ∅`. -/
def D1Stmt : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (p : ℕ) (hp : p < gates.length),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    AtMostOneNot gates → (gates[p]'hp).op = GateOp.not →
    ∀ (R R' : Finset (Fin n)) (o o' : ℕ), (R ∩ R').card ≤ 1 →
    (∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) →
    (∀ x : Fin n → Bool, val gates x o' = decide (∃ v ∈ R', x v = true)) →
    ∀ (Z : Fin n → Bool), (∀ c ∈ R, Z c = false) → val gates Z (n + p) = true →
    (∀ c, c ∉ R → Z c = false → val gates (Function.update Z c true) (n + p) = false) →
    ∀ (m : Fin n → Finset (Fin n)),
    (∀ u ∈ R', val gates (canonPt (m u)) (n + p) = false ∧
      (∀ c ∈ m u, val gates (canonPt ((m u).erase c)) (n + p) = true) ∧
      m u ∩ R' ⊆ {u} ∧ Disjoint (m u) R) →
    Disjoint (K1Z gates p R Z) (K0of gates p R' m)

/-- The counterexample circuit on `n = 5` (wires `0..4` inputs, wire `5 + k` gate `k`):
`y = ¬x_4`; `P = (y ∧ x_0) ∨ (x_4 ∧ x_2)`; `Q = (y ∧ x_1) ∨ (x_4 ∧ x_3)`; `g = P ∨ Q` (wire 12);
outputs `x_0 ∨ x_1` (wire 13) and `x_2 ∨ x_3` (wire 14). -/
def ceGates : List Gate :=
  [⟨GateOp.not, [4]⟩, ⟨GateOp.and, [5, 0]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [6, 7]⟩,
   ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [8, 11]⟩,
   ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩]

def ceR : Finset (Fin 5) := {0, 1}
def ceR' : Finset (Fin 5) := {2, 3}
/-- `Z = top_w \ {4}`: true exactly on `{2, 3}`. -/
def ceZ : Fin 5 → Bool := canonPt {2, 3}
def ceM : Fin 5 → Finset (Fin 5) := fun _ => {4}

theorem ce_hg : ∀ g ∈ ceGates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [ceGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ce_hU : AtMostOneNot ceGates := by
  have key : ∀ i (h : i < ceGates.length), (ceGates[i]'h).op = GateOp.not → i = 0 := by
    intro i h
    have h' : i < 10 := h
    interval_cases i <;> simp [ceGates]
  intro i1 i2 h1 h2 e1 e2
  rw [key i1 h1 e1, key i2 h2 e2]

theorem ce_hp : 0 < ceGates.length := by simp [ceGates]

theorem ce_hN : (ceGates[0]'ce_hp).op = GateOp.not := rfl

/-- Both atoms of a two-element set, enumerated by `enumF`. -/
theorem enumF_cases (R : Finset (Fin 5)) (a b : Fin 5) (hR : R = {a, b}) (t : Fin R.card) :
    enumF R t = a ∨ enumF R t = b := by
  have key : ∀ c ∈ R, c = a ∨ c = b := by rw [hR]; simp
  exact key _ (enumF_mem R t)

theorem card_atomsAt_of_all {N k : ℕ} (gs : List Gate) (a : Fin k → Fin N → Bool) (i : ℕ)
    (h : ∀ t, val gs (a t) i = true) : (atomsAt gs a i).card = k := by
  have : atomsAt gs a i = Finset.univ := by
    ext t; simp [mem_atomsAt, h t]
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- The gate `g` (wire 12; gate 6 of the lift) lies in `K_1(w; Z) ∩ K_0(v; m)`. -/
theorem ce_mem : 12 ∈ K1Z ceGates 0 ceR ceZ ∩ K0of ceGates 0 ceR' ceM := by
  have hw : realWire 5 0 6 = 12 := rfl
  rw [Finset.mem_inter, K1Z, K0of]
  constructor
  · refine Finset.mem_image.mpr ⟨6, mem_orClz.mpr ⟨by decide, ⟨_, rfl, rfl⟩, by decide, ?_⟩, hw⟩
    rw [card_atomsAt_of_all]
    · decide
    · intro t
      rcases enumF_cases ceR 0 1 rfl t with h | h <;> rw [h] <;> decide
  · refine Finset.mem_image.mpr ⟨6, mem_orClz.mpr ⟨by decide, ⟨_, rfl, rfl⟩, by decide, ?_⟩, hw⟩
    rw [card_atomsAt_of_all]
    · decide
    · intro t
      rcases enumF_cases ceR' 2 3 rfl t with h | h <;> rw [h] <;> decide

/-- **D1 is false**: the circuit `ceGates` is a correct one-NOT circuit for the sets
`{0,1}`, `{2,3}`, `Z = {2,3}` is an I1 point of `{0,1}` (`h = x_4`), `m_2 = m_3 = {4}` is an I0
choice of `{2,3}` avoiding `{0,1}`, and wire 12 is in both classes. -/
theorem not_D1Stmt : ¬ D1Stmt := by
  intro H
  have hd := H 5 ceGates 0 ce_hp ce_hg ce_hU ce_hN ceR ceR' 13 14 (by decide)
    (by decide) (by decide) ceZ (by decide) (by decide) (by decide) ceM (by decide)
  exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp ce_mem).1 (Finset.mem_inter.mp ce_mem).2

end PEqualNP.Outside.L_meta_951_aux

end CanonD1

section MergeLink

/-! MergeLink: the load condition `hload` of `liftClassFrac_of_realBasePoints` (LiftHelpers) gives
MergeFrac, with the same weights.

The two `no_minCE` targets on the fractional route charge different sets at the same points:
* `hload` (LiftHelpers): weights `lam w j` on zero points `z w j` of `S w`, and every gate `i ≠ p`
  has load `≤ 1` over the WHOLE classes `RealCl gates p (S w) (z w j) i` (OR gate, `0` at `z`,
  `1` at two or more `z + e_u`, `u ∈ S w`, read in the world of `z`); it gives `LiftClassFrac`,
  hence `s ≥ base + 1`.
* `MergeFrac` (MergeFrac.lean): distributions on zero points, and every wire has load `≤ 1` over
  the MERGE SETS `M_z(w)` (exactly `|S w| - 1` gates, Lemma M); it gives `FracMatch`, hence
  `s ≥ base`. `MergePrice` is its LP dual (`mergeFrac_iff_mergePrice`).

`realCl_of_mem_mergeSet`: every merge gate of `S` at a zero point `z` is in the class `RealCl` of
`z` (merges are OR gates, `mergeSet_or`; the NOT gate is not an OR gate; the real circuit lies
between the worlds `C0 ≤ real ≤ C1`, and on `{h = 1}` it equals `C0`). Hence
`mergeFrac_of_realBasePoints`: a weighting that satisfies `hload` satisfies MergeFrac. So
`MergeFrac` / `MergePrice` is the weaker target, and every result on either route lands in
`no_minCE_of_mergePrice`. The converse fails as a method: whole-class charging is refuted on cxT2
and cxT4 (front-match w9/chist_fable.md C1), while MergeFrac holds on every circuit checked
(about 15,300, C6). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

open Classical in
/-- **Merge sets lie in the real-base-point classes.** For the NOT gate at `p` and a point `z`
vanishing on `R`, every merge gate `n + i` of `R` at `z` is in `RealCl gates p R z i`. -/
theorem realCl_of_mem_mergeSet {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (R : Finset (Fin n))
    (z : Fin n → Bool) (i : ℕ) (hi : n + i ∈ mergeSet gates R z) : RealCl gates p R z i := by
  obtain ⟨hil, hor⟩ := mergeSet_or gates hg hU R z i hi
  have hD := mergeSet_subset_DT gates R z hi
  simp only [DT, Finset.mem_filter] at hD
  obtain ⟨-, hz, u, v, huv, hu, hv, hgu, hgv⟩ := hD
  have hip : i ≠ p := by
    rintro rfl
    rw [hN] at hor
    exact GateOp.noConfusion hor
  -- a real `1` at a test point is a `1` in the world of `z`
  have hworld : ∀ x, z ≤ x → val gates x (n + i) = true →
      val (wld (!hval gates p z) gates) x (n + i) = true := by
    intro x hzx hx
    cases hh : hval gates p z
    · simp only [Bool.not_false, wld, ite_true]
      exact ((sandwich gates (fun g hg' => (hg g hg').1) x) (n + i)).2 hx
    · simp only [Bool.not_true]
      rw [val_wld_false_of_hval gates p hp hU hN x
        (hval_mono gates p hp hg hU hN hzx hh) (n + i)]
      exact hx
  refine ⟨hil, hip, ⟨gates[i]'hil, List.getElem?_eq_getElem hil, hor⟩, hz,
    Finset.one_lt_card.mpr ⟨u, ?_, v, ?_, huv⟩⟩
  · exact Finset.mem_filter.mpr ⟨hu, hworld _ (le_upPt z u) hgu⟩
  · exact Finset.mem_filter.mpr ⟨hv, hworld _ (le_upPt z v) hgv⟩

open Classical in
/-- **`hload` gives MergeFrac.** The load hypothesis of `liftClassFrac_of_realBasePoints` (weights
`lam w j` on zero points `z w j`, whole classes `RealCl`, load `≤ 1` at every gate `i ≠ p`)
implies `MergeFrac`, with `μ w` the same mixture of the points `z w j`. -/
theorem mergeFrac_of_realBasePoints {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if RealCl gates p (S w) (z w j) i then lam w j else 0) ≤ 1) :
    MergeFrac S gates := by
  refine ⟨fun w x => ∑ j, if z w j = x then lam w j else 0, ?_, ?_, ?_, ?_⟩
  · intro w x
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hlam0]
  · rintro w x ⟨v, hv, hxv⟩
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    rintro rfl
    rw [hz w j v hv] at hxv
    exact absurd hxv (by simp)
  · intro w
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hlam1 w
  · intro g
    -- the load of `g` is the load over the points `z w j`
    have hre : ∀ w, ∑ x, (if g ∈ mergeSet gates (S w) x then
        ∑ j, (if z w j = x then lam w j else 0) else 0) =
        ∑ j, (if g ∈ mergeSet gates (S w) (z w j) then lam w j else 0) := by
      intro w
      trans ∑ x, ∑ j, (if z w j = x then
          (if g ∈ mergeSet gates (S w) x then lam w j else 0) else 0)
      · refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hg : g ∈ mergeSet gates (S w) x
        · simp only [hg, ite_true]
        · simp only [hg, ite_false, ite_self, Finset.sum_const_zero]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    simp only [hre]
    by_cases hex : ∃ i, i < gates.length ∧ i ≠ p ∧ g = n + i
    · obtain ⟨i, hi, hip, rfl⟩ := hex
      refine le_trans (Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun j _ => ?_)
        (hload i hi hip)
      by_cases hm : n + i ∈ mergeSet gates (S w) (z w j)
      · rw [ite_eq_left hm, ite_eq_left (realCl_of_mem_mergeSet gates p hp hg hU hN (S w) (z w j) i hm)]
      · rw [ite_eq_right hm]
        split_ifs
        · exact hlam0 w j
        · exact le_rfl
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun j _ => ?_)
        zero_le_one
      rw [ite_eq_right]
      intro hm
      have hI := Finset.mem_Ico.mp (mergeSet_subset gates (S w) (z w j) hm)
      obtain ⟨i, rfl⟩ : ∃ i, g = n + i := ⟨g - n, by omega⟩
      have hR := realCl_of_mem_mergeSet gates p hp hg hU hN (S w) (z w j) i hm
      exact hex ⟨i, hR.1, hR.2.1, rfl⟩

open Classical in
/-- **`hload` gives MergePrice** (the price form front attacks), by LP duality. -/
theorem mergePrice_of_realBasePoints {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if RealCl gates p (S w) (z w j) i then lam w j else 0) ≤ 1) :
    MergePrice S gates :=
  mergePrice_of_mergeFrac S gates
    (mergeFrac_of_realBasePoints S gates p hp hg hU hN k z lam hlam0 hlam1 hz hload)

end PEqualNP.Outside.L_meta_951_aux

end MergeLink
