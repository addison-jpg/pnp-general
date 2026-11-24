import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.LiftFrac

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
