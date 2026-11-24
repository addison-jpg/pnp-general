import PEqualNP.Kernel.Privacy

/-!
# Kernel/AndReplace: Wegener's AND-replacement (Theorem 6.2, `h = k = 1`) at a base point

Wegener, *The Complexity of Boolean Functions*, §6.6, Theorem 6.2 / Corollary 6.1: AND gates do
not help for `(1,1)`-disjoint Boolean sums. Here generically over `Dag n s`, relative to a base
point `z` (the cube `{x ≥ z}`), for AND/OR dags of fan-in `≤ 2` (constants allowed as inputs).

* `replaceGate D i g'`: the kernel pass replacing gate `i` by `g'` (same shape, same size), with
  `val_replaceGate_of_lt` (wires below gate `i` are untouched) and `val_replaceGate_self`.
* `exists_dep`: if every gate after `i` is an OR gate (`i` is the LAST AND gate), then every wire
  `w` has a constant `c w` such that for every replacement `g'` and every input,
  `val (D[i := g']) w = val (D[i := 0]) w ∨ (c w ∧ g')` (Wegener's `f_j = g ∨ h_j`).
* `exists_replace_and` (the step): outputs computing a `(1,1)`-disjoint Boolean sum on
  `{x ≥ z}`; the last AND gate can be replaced by a one-input OR gate (`s`, `t`, the single
  variable of its length-1 part, or a constant), keeping all outputs correct on `{x ≥ z}`.
  - the length-1 part `I = supp z G` has at most one element: replace `G` by `OR I`
    (Wegener's first replacement rule, proved directly);
  - `|I| ≥ 2`: at most one output depends on `G` (privacy), and (6.7) = `boolSum_and_split`
    replaces `G = s ∧ t` by `s` or by `t`.
* `sum_card_sub_one_le_andOr`: induction on the number of AND gates (`andGates`), ending with
  `sum_card_sub_one_le_gates`: `Σ_{w ∈ T} (|S w| − 1) ≤ s`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open Function (update)

/-- **OR gates are affine in a distinguished value.** If every wire value has the form
`v a = v0 a ∨ (c a ∧ G)`, so has the value of an OR gate, with `c` the OR of the `c a` over the
wires read. -/
theorem KGate.eval_or_dep {k : ℕ} {g : KGate k} (hg : g.op = GateOp.or) (v v0 : Fin k → Bool)
    (c : Fin k → Bool) (G : Bool) (h : ∀ a, v a = (v0 a || (c a && G))) :
    g.eval v = (g.eval v0 || (g.inputs.any (fun s => s.wire?.elim false c) && G)) := by
  rw [eval_def, eval_def, hg]
  show (g.inputs.map (Src.eval v)).any id =
    ((g.inputs.map (Src.eval v0)).any id || (g.inputs.any (fun s => s.wire?.elim false c) && G))
  induction g.inputs with
  | nil => rfl
  | cons s l ih =>
    simp only [List.map_cons, List.any_cons, ih, id]
    cases s with
    | wire a =>
      simp only [Src.eval_wire, Src.wire?_wire, Option.elim, h a]
      cases v0 a <;> cases c a <;> cases G <;> simp
    | const b =>
      simp only [Src.eval_const, Src.wire?_const, Option.elim]
      cases b <;> simp

namespace Dag

variable {n s : ℕ}

/-! ## The pass: replace one gate -/

/-- Replace gate `i` by `g'`. -/
def replaceGate (D : Dag n s) (i : Fin s) (g' : KGate (n + i)) : Dag n s :=
  ⟨Function.update D.gate i g'⟩

@[simp] theorem replaceGate_gate_self (D : Dag n s) (i : Fin s) (g' : KGate (n + i)) :
    (D.replaceGate i g').gate i = g' := Function.update_self _ _ _

theorem replaceGate_gate_of_ne (D : Dag n s) (i : Fin s) (g' : KGate (n + i)) {j : Fin s}
    (h : j ≠ i) : (D.replaceGate i g').gate j = D.gate j := Function.update_of_ne h _ _

@[simp] theorem replaceGate_self (D : Dag n s) (i : Fin s) : D.replaceGate i (D.gate i) = D := by
  ext j
  simp [replaceGate]

/-- Wires below the replaced gate keep their values. -/
theorem val_replaceGate_of_lt (D : Dag n s) (i : Fin s) (g' : KGate (n + i)) (x : Fin n → Bool)
    (w : Fin (n + s)) (hw : w.1 < n + i) : (D.replaceGate i g').val x w = D.val x w := by
  refine agree_off₂ (D.replaceGate i g') D x x (fun w => n + i ≤ w.1) (fun _ _ => rfl)
    (fun j hj => ?_) w (by omega)
  have hj' : j.1 < i.1 := by simpa using hj
  refine ⟨D.replaceGate_gate_of_ne i g' (by rintro rfl; omega), fun a _ => ?_⟩
  have := a.2
  show ¬ (n + i.1 ≤ a.1)
  omega

/-- The replaced gate computes `g'` on the old wire values. -/
theorem val_replaceGate_self (D : Dag n s) (i : Fin s) (g' : KGate (n + i)) (x : Fin n → Bool) :
    (D.replaceGate i g').val x (Fin.natAdd n i) = g'.eval fun a => D.val x (lift i a) := by
  rw [val_natAdd, replaceGate_gate_self]
  exact KGate.eval_congr fun a _ => D.val_replaceGate_of_lt i g' x _ a.2

/-- **Wegener's `f = g ∨ h`.** If every gate after `i` is an OR gate, each wire `w` has a
constant `c` ("`w` is a successor of gate `i`") such that, for every replacement `g'` of gate
`i` and every input `x`, the value of `w` is its value with gate `i` replaced by `0`, OR
(`c` AND the value of `g'`). -/
theorem exists_dep (D : Dag n s) (i : Fin s)
    (hor : ∀ j, i < j → (D.gate j).op = GateOp.or) :
    ∀ w, ∃ c : Bool, ∀ (g' : KGate (n + i)) (x : Fin n → Bool),
      (D.replaceGate i g').val x w =
        ((D.replaceGate i (KGate.const false)).val x w ||
          (c && g'.eval fun a => D.val x (lift i a))) := by
  refine wire_induction (fun j => ⟨false, fun g' x => by simp⟩) (fun j ih => ?_)
  rcases lt_trichotomy j i with h | rfl | h
  · refine ⟨false, fun g' x => ?_⟩
    have hlt : (Fin.natAdd n j).1 < n + i := Nat.add_lt_add_left h n
    rw [D.val_replaceGate_of_lt i _ x _ hlt, D.val_replaceGate_of_lt i _ x _ hlt]
    simp
  · refine ⟨true, fun g' x => ?_⟩
    rw [val_replaceGate_self, val_replaceGate_self]
    simp
  · choose c hc using ih
    refine ⟨(D.gate j).inputs.any (fun s => s.wire?.elim false c), fun g' x => ?_⟩
    rw [val_natAdd, val_natAdd, D.replaceGate_gate_of_ne i _ (ne_of_gt h),
      D.replaceGate_gate_of_ne i _ (ne_of_gt h)]
    exact KGate.eval_or_dep (hor j h) _ _ c _ fun a => hc a g' x

/-! ## The step: eliminating the last AND gate -/

/-- **Wegener, Theorem 6.2, the replacement step (`h = k = 1`, base `z`).** An AND/OR dag of
fan-in `≤ 2` whose outputs `o w` (`w ∈ T`) compute a `(1,1)`-disjoint Boolean sum on `{x ≥ z}`
(each `S w` missing `z`). If gate `i` is an AND gate and all later gates are OR gates, then gate
`i` can be replaced by a one-input OR gate (an input of gate `i`, an input variable, or a
constant) such that all the outputs still compute their sums on `{x ≥ z}`. -/
theorem exists_replace_and (D : Dag n s)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2) (i : Fin s)
    (hand : (D.gate i).op = GateOp.and) (hor : ∀ j, i < j → (D.gate j).op = GateOp.or)
    (z : Fin n → Bool) {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) z = false) :
    ∃ p : Src (n + i), ∀ w ∈ T, ∀ x, z ≤ x →
      (D.replaceGate i ⟨GateOp.or, [p]⟩).val x (o w) = orOf (S w) x := by
  classical
  choose c hc using D.exists_dep i hor
  set D0 := D.replaceGate i (KGate.const false) with hD0def
  have hD0 : D0.Mono := fun j => by
    by_cases hj : j = i
    · subst hj
      rw [hD0def, replaceGate_gate_self]
      exact KGate.opMono_const false
    · rw [hD0def, D.replaceGate_gate_of_ne i _ hj]
      exact opMono_of_and_or (hD j)
  have hDm : D.Mono := D.mono_of_and_or hD
  -- the value of `D` itself
  have hval : ∀ w x, D.val x w = (D0.val x w || (c w && D.val x (Fin.natAdd n i))) := by
    intro w x
    have := hc w (D.gate i) x
    rwa [replaceGate_self, ← val_natAdd] at this
  have heval : ∀ (p : Src (n + i)) (v : Fin (n + i) → Bool),
      (⟨GateOp.or, [p]⟩ : KGate (n + i)).eval v = p.eval v := by
    intro p v
    simp [KGate.eval_def, GateOp.eval]
  -- it suffices to treat the outputs that depend on gate `i`
  have key : ∀ p : Src (n + i),
      (∀ w ∈ T, c (o w) = true → ∀ x, z ≤ x →
        orOf (S w) x = (D0.val x (o w) || p.eval fun a => D.val x (lift i a))) →
      ∀ w ∈ T, ∀ x, z ≤ x →
        (D.replaceGate i ⟨GateOp.or, [p]⟩).val x (o w) = orOf (S w) x := by
    intro p hp w hw x hx
    rw [hc (o w) _ x, heval]
    cases hcw : c (o w)
    · rw [← ho w hw x hx, hval (o w) x, hcw]
      simp
    · simpa using (hp w hw hcw x hx).symm
  -- a dependent output forces gate `i` off at `z`
  have gz : ∀ w ∈ T, c (o w) = true → D.val z (Fin.natAdd n i) = false := by
    intro w hw hcw
    have := hval (o w) z
    rw [ho w hw z le_rfl, hz w hw, hcw] at this
    revert this
    cases D0.val z (o w) <;> cases D.val z (Fin.natAdd n i) <;> simp
  have hu : ∀ (x : Fin n → Bool), z ≤ x → ∀ v, x v = true → update z v true ≤ x := by
    intro x hx v hxv k
    by_cases hk : k = v
    · subst hk; simp [hxv]
    · rw [Function.update_of_ne hk]; exact hx k
  -- the first replacement rule: `g` may be replaced by its length-1 part
  have L : ∀ w ∈ T, c (o w) = true → ∀ x, z ≤ x →
      orOf (S w) x = (D0.val x (o w) || orOf (D.supp z (Fin.natAdd n i)) x) := by
    intro w hw hcw x hx
    rw [Bool.eq_iff_iff]
    constructor
    · intro h
      simp only [orOf, decide_eq_true_eq] at h
      obtain ⟨v, hv, hxv⟩ := h
      have hzv : z v = false := by
        have := hz w hw
        simp only [orOf, decide_eq_false_iff_not, not_exists, not_and] at this
        simpa using this v hv
      have h1 := hval (o w) (update z v true)
      have h1t : orOf (S w) (update z v true) = true := by
        simp only [orOf, decide_eq_true_eq]
        exact ⟨v, hv, by simp⟩
      rw [ho w hw _ (le_update z v), hcw, h1t] at h1
      cases h0 : D0.val (update z v true) (o w)
      · have hg : D.val (update z v true) (Fin.natAdd n i) = true := by
          rw [h0] at h1; simpa using h1.symm
        have hvI : v ∈ D.supp z (Fin.natAdd n i) := mem_supp.mpr ⟨hzv, hg, gz w hw hcw⟩
        have : orOf (D.supp z (Fin.natAdd n i)) x = true := by
          simp only [orOf, decide_eq_true_eq]
          exact ⟨v, hvI, hxv⟩
        rw [this]; simp
      · have := Bool.le_iff_imp.mp (D0.val_mono hD0 (hu x hx v hxv) (o w)) h0
        rw [this]; simp
    · intro h
      rw [← ho w hw x hx, hval (o w) x, hcw]
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simp [h]
      · simp only [orOf, decide_eq_true_eq] at h
        obtain ⟨v, hv, hxv⟩ := h
        obtain ⟨_, hg, _⟩ := mem_supp.mp hv
        have := Bool.le_iff_imp.mp (D.val_mono hDm (hu x hx v hxv) (Fin.natAdd n i)) hg
        simp [this]
  set I := D.supp z (Fin.natAdd n i) with hIdef
  by_cases hI : I.card ≤ 1
  · -- the length-1 part is a constant or a variable
    have hp : ∃ p : Src (n + i), ∀ x, (p.eval fun a => D.val x (lift i a)) = orOf I x := by
      rcases I.eq_empty_or_nonempty with h | ⟨v, hv⟩
      · exact ⟨Src.const false, fun x => by simp [h, orOf]⟩
      · have hIv : I = {v} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hv, fun u hu => Finset.card_le_one.mp hI u hu v hv⟩
        refine ⟨Src.wire ⟨v.1, by omega⟩, fun x => ?_⟩
        have e : lift i (⟨v.1, by omega⟩ : Fin (n + i)) = Fin.castAdd s v := Fin.ext rfl
        rw [Src.eval_wire, e, val_castAdd, hIv]
        simp [orOf]
    obtain ⟨p, hp⟩ := hp
    exact ⟨p, key p fun w hw hcw x hx => by rw [hp]; exact L w hw hcw x hx⟩
  · push Not at hI
    by_cases hex : ∃ a ∈ T, c (o a) = true
    swap
    · exact ⟨Src.const false, key _ fun w hw hcw => absurd ⟨w, hw, hcw⟩ hex⟩
    obtain ⟨a, haT, hca⟩ := hex
    -- privacy: only the output `a` depends on gate `i`
    have hle : ∀ w ∈ T, c (o w) = true → I ⊆ S w := fun w hw hcw =>
      D.supp_subset_of_le z (ho w hw) (hz w hw) fun x _ => by
        rw [hval (o w) x, hcw, Bool.le_iff_imp]
        intro h; simp [h]
    have huniq : ∀ w ∈ T, c (o w) = true → w = a := by
      intro w hw hcw
      by_contra hne
      have h1 := hdisj w hw a haT hne
      have h2 := Finset.card_le_card (Finset.subset_inter (hle w hw hcw) (hle a haT hca))
      omega
    suffices hs : ∃ p : Src (n + i), ∀ x, z ≤ x →
        orOf (S a) x = (D0.val x (o a) || p.eval fun b => D.val x (lift i b)) by
      obtain ⟨p, hp⟩ := hs
      exact ⟨p, key p fun w hw hcw => by rw [huniq w hw hcw]; exact hp⟩
    have hga : ∀ x, D.val x (Fin.natAdd n i) =
        ((D.gate i).inputs.map (Src.eval fun b => D.val x (lift i b))).all id := fun x => by
      rw [val_natAdd, KGate.eval_def, hand]; rfl
    have hfi := hfan i
    have hgz := gz a haT hca
    have hfa : ∀ x, D.val x (o a) = (D0.val x (o a) || D.val x (Fin.natAdd n i)) := fun x => by
      rw [hval (o a) x, hca]; simp
    rcases hl : (D.gate i).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
    · rw [hga, hl] at hgz
      simp at hgz
    · refine ⟨p, fun x hx => ?_⟩
      rw [← ho a haT x hx, hfa x, hga, hl]
      simp
    · have hsm : ∀ (p : Src (n + i)) (x y : Fin n → Bool), x ≤ y →
          (p.eval fun b => D.val x (lift i b)) ≤ p.eval fun b => D.val y (lift i b) := by
        intro p x y hxy
        cases p with
        | wire b => exact D.val_mono hDm hxy _
        | const b => exact le_rfl
      have hsplit := boolSum_and_split (A := fun x => z ≤ x)
        (fun x y hx _ => le_trans hx le_sup_left) (S := S a)
        (f := fun x => D.val x (o a))
        (s := fun x => p.eval fun b => D.val x (lift i b))
        (t := fun x => q.eval fun b => D.val x (lift i b))
        (h := fun x => D0.val x (o a))
        (fun x hx => ho a haT x hx)
        (fun x _ => by
          show D.val x (o a) = _
          rw [hfa x, hga, hl]
          simp [Bool.or_comm])
        (fun x y _ _ h => hsm p x y h) (fun x y _ _ h => hsm q x y h)
      rcases hsplit with h | h
      · exact ⟨p, fun x hx => by rw [← ho a haT x hx, Bool.or_comm]; exact h x hx⟩
      · exact ⟨q, fun x hx => by rw [← ho a haT x hx, Bool.or_comm]; exact h x hx⟩
    · rw [hl] at hfi
      simp at hfi

/-! ## The induction on the number of AND gates -/

open Classical in
/-- The AND gates of a dag (the induction measure is its cardinality). -/
noncomputable def andGates (D : Dag n s) : Finset (Fin s) :=
  Finset.univ.filter fun i => (D.gate i).op = GateOp.and

theorem mem_andGates {D : Dag n s} {i : Fin s} :
    i ∈ D.andGates ↔ (D.gate i).op = GateOp.and := by
  classical
  simp [andGates]

/-- Replacing an AND gate by an OR gate removes it from the AND gates. -/
theorem andGates_replaceGate_subset (D : Dag n s) (i : Fin s) (g' : KGate (n + i))
    (hg' : g'.op = GateOp.or) : (D.replaceGate i g').andGates ⊆ D.andGates.erase i := by
  intro j hj
  rw [mem_andGates] at hj
  by_cases h : j = i
  · subst h
    rw [replaceGate_gate_self, hg'] at hj
    exact absurd hj (by simp)
  · rw [D.replaceGate_gate_of_ne i g' h] at hj
    exact Finset.mem_erase.mpr ⟨h, mem_andGates.mpr hj⟩

/-- **Wegener, Theorem 6.2 / Corollary 6.1 (`h = k = 1`), at base `z`: the exact Nechiporuk
bound for monotone circuits.** An AND/OR dag of fan-in `≤ 2` (constants allowed) whose outputs
`o w` (`w ∈ T`) compute Boolean sums `OR (S w)` on the cube `{x ≥ z}`, each `S w` missing `z`,
pairwise sharing at most one variable, has at least `Σ_{w ∈ T} (|S w| − 1)` gates. -/
theorem sum_card_sub_one_le_andOr (D : Dag n s)
    (hD : ∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or)
    (hfan : ∀ j, (D.gate j).inputs.length ≤ 2)
    (z : Fin n → Bool) {ι : Type*} (T : Finset ι) (o : ι → Fin (n + s))
    (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x)
    (hz : ∀ w ∈ T, orOf (S w) z = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ s := by
  suffices key : ∀ m : ℕ, ∀ D : Dag n s,
      (∀ j, (D.gate j).op = GateOp.and ∨ (D.gate j).op = GateOp.or) →
      (∀ j, (D.gate j).inputs.length ≤ 2) →
      (∀ w ∈ T, ∀ x, z ≤ x → D.val x (o w) = orOf (S w) x) →
      D.andGates.card ≤ m → ∑ w ∈ T, ((S w).card - 1) ≤ s from
    key _ D hD hfan ho le_rfl
  intro m
  induction m with
  | zero =>
    intro D hD hfan ho hm
    have hOr : D.OrOnly := fun j => (hD j).resolve_left fun h => by
      have := Finset.card_pos.mpr ⟨j, mem_andGates.mpr h⟩
      omega
    have := D.sum_card_sub_one_le_gates hOr hfan z T o S hdisj ho hz
    exact this.1.trans this.2
  | succ m ih =>
    intro D hD hfan ho hm
    by_cases hne : D.andGates.Nonempty
    swap
    · exact ih D hD hfan ho (by rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp)
    -- the last AND gate
    set i := D.andGates.max' hne with hi
    have hand : (D.gate i).op = GateOp.and := mem_andGates.mp (D.andGates.max'_mem hne)
    have hor : ∀ j, i < j → (D.gate j).op = GateOp.or := fun j hj =>
      (hD j).resolve_left fun h =>
        absurd (D.andGates.le_max' j (mem_andGates.mpr h)) (not_le.mpr hj)
    obtain ⟨p, hp⟩ := D.exists_replace_and hD hfan i hand hor z T o S hdisj ho hz
    refine ih (D.replaceGate i ⟨GateOp.or, [p]⟩) (fun j => ?_) (fun j => ?_) hp ?_
    · by_cases h : j = i
      · subst h; rw [replaceGate_gate_self]; exact Or.inr rfl
      · rw [D.replaceGate_gate_of_ne i _ h]; exact hD j
    · by_cases h : j = i
      · subst h; rw [replaceGate_gate_self]; simp
      · rw [D.replaceGate_gate_of_ne i _ h]; exact hfan j
    · have h1 := Finset.card_le_card (D.andGates_replaceGate_subset i ⟨GateOp.or, [p]⟩ rfl)
      have h2 := Finset.card_erase_add_one (D.andGates.max'_mem hne)
      rw [← hi] at h2
      omega

end Dag

end PEqualNP.Kernel
