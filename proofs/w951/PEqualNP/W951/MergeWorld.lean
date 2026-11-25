import PEqualNP.W951.MergeFrac
import PEqualNP.Kernel.W951TwoWorld
import PEqualNP.W951.LiftHelpers

/-! MergeWorld: the world split of the merge sets (coord assignment, reset 2026-11-24; Lean basis
for the cross-world load, the missing piece of `no_minCE`).

A zero point `z` of a set `R` is classified by the NOT gates (at most one; with one NOT gate
reading `h`, the NOT gate is `¬ h`):
* world-0 (`World0`): every NOT gate is `0` at `z` (`h z = 1`);
* world-1 (`World1`): every NOT gate is `1` at every test point `z + e_u`, `u ∈ R`
  (`h (z + e_u) = 0` for all `u ∈ R`);
* mixed (`Mixed`): neither.

Results:
1. Classification: `world_trichotomy`; `notsAt_iff_of_not` (the NOT-gate form, one NOT gate);
   `not_world0_and_world1` (the two worlds are exclusive when there is a NOT gate and `R ≠ ∅`).
2. Values: at a world-0 point every wire of the circuit agrees with `C0` (NOT := 0) on the whole
   up-cube of `z` (`World0.val_C0`); at a world-1 point every wire agrees with `C1` (NOT := 1)
   below every test point `z + e_u`, in particular at `z` and at each `z + e_u`
   (`World1.val_C1`). Both come from `Kernel.C0_agree_of_not_false` / `C1_agree_of_not_true`.
3. Merge sets: the union-find run reads the circuit only through the wire values at `z` and at
   the test points (`run_congr`, `mergeSet_congr`), so `M_z(R)` of the real circuit equals
   `M_z(R)` of the monotone circuit `C0` at a world-0 point (`mergeSet_C0_of_world0`) and of `C1`
   at a world-1 point (`mergeSet_C1_of_world1`).
4. `NoMixedFrac`: `MergeFrac` with every `μ_w` supported on non-mixed zero points;
   `mergeFrac_of_noMixedFrac`. The load of a no-mixed `μ` splits into a `C0` part (world-0
   points) and a `C1` part (the other non-mixed points): `noMixed_load_eq`, `noMixedFrac_iff`.
5. The classification in terms of `h = hval gates p` (LiftHelpers): `world0_iff_hval`
   (`h z = 1`), `world1_iff_hval` (`h (z + e_u) = 0` for every `u ∈ R`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section World

variable {n : ℕ}

/-- Every NOT gate of the circuit outputs `b` at `x`. With one NOT gate reading `h`,
`NotsAt gates x false` is `h x = 1` and `NotsAt gates x true` is `h x = 0`. A circuit without
NOT gates satisfies `NotsAt gates x b` for every `x` and `b`. -/
def NotsAt (gates : List Gate) (x : Fin n → Bool) (b : Bool) : Prop :=
  ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not → val gates x (n + p) = b

/-- A world-0 zero point: every NOT gate is `0` at `z` (one NOT gate reading `h`: `h z = 1`). -/
def World0 (gates : List Gate) (z : Fin n → Bool) : Prop :=
  NotsAt gates z false

/-- A world-1 zero point of `R`: every NOT gate is `1` at every test point `z + e_u`, `u ∈ R`
(one NOT gate reading `h`: `h (z + e_u) = 0` for every `u ∈ R`). -/
def World1 (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  ∀ u ∈ R, NotsAt gates (upPt z u) true

/-- A mixed zero point of `R`: neither world-0 nor world-1. -/
def Mixed (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  ¬ World0 gates z ∧ ¬ World1 gates R z

theorem world_trichotomy (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    World0 gates z ∨ World1 gates R z ∨ Mixed gates R z := by
  unfold Mixed
  by_cases h0 : World0 gates z
  · exact Or.inl h0
  · by_cases h1 : World1 gates R z
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h0, h1⟩)

/-- With one NOT gate (at position `p`), `NotsAt` is the value of that gate. -/
theorem notsAt_iff_of_not {gates : List Gate} (hU : AtMostOneNot gates) {p : ℕ}
    (hp : p < gates.length) (hN : (gates[p]'hp).op = GateOp.not) (x : Fin n → Bool) (b : Bool) :
    NotsAt gates x b ↔ val gates x (n + p) = b := by
  constructor
  · intro h
    exact h p hp hN
  · intro h q hq hq'
    rw [hU q p hq hp hq' hN]
    exact h

/-- Without NOT gates every point is in both worlds. -/
theorem notsAt_of_noNot {gates : List Gate} (h : ∀ g ∈ gates, g.op ≠ GateOp.not)
    (x : Fin n → Bool) (b : Bool) : NotsAt gates x b :=
  fun _ hp hN => absurd hN (h _ (List.getElem_mem hp))

variable {gates : List Gate}
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

include hg hU

/-- The two worlds are exclusive when there is a NOT gate and `R` is nonempty. -/
theorem not_world0_and_world1 {p : ℕ} (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) {R : Finset (Fin n)} (hR : R.Nonempty)
    (z : Fin n → Bool) : ¬ (World0 gates z ∧ World1 gates R z) := by
  rintro ⟨h0, h1⟩
  obtain ⟨u, hu⟩ := hR
  have h := PEqualNP.Kernel.not_val_anti hg hU p hp hN (le_upPt z u) (h1 u hu p hp hN)
  rw [h0 p hp hN] at h
  exact absurd h (by simp)

/-- At a world-1 point of a nonempty set, every NOT gate is `1` at `z` itself. -/
theorem World1.notsAt_zero {R : Finset (Fin n)} {z : Fin n → Bool} (h1 : World1 gates R z)
    (hR : R.Nonempty) : NotsAt gates z true := by
  obtain ⟨u, hu⟩ := hR
  intro p hp hN
  exact PEqualNP.Kernel.not_val_anti hg hU p hp hN (le_upPt z u) (h1 u hu p hp hN)

/-- **World 0.** At a world-0 point every wire of the circuit equals its `C0` value (NOT := 0)
on the whole up-cube of `z`. -/
theorem World0.val_C0 {z : Fin n → Bool} (h0 : World0 gates z) :
    ∀ x, z ≤ x → ∀ i, val gates x i = val (C0 gates) x i :=
  fun x hx i => (PEqualNP.Kernel.C0_agree_of_not_false gates hg hU z h0 x hx i).symm

/-- **World 1.** At a world-1 point of `R` every wire of the circuit equals its `C1` value
(NOT := 1) below every test point `z + e_u`, `u ∈ R`: at `z` and at every `z + e_u`. -/
theorem World1.val_C1 {R : Finset (Fin n)} {z : Fin n → Bool} (h1 : World1 gates R z) :
    ∀ u ∈ R, ∀ x, x ≤ upPt z u → ∀ i, val gates x i = val (C1 gates) x i :=
  fun u hu x hx i =>
    (PEqualNP.Kernel.C1_agree_of_not_true gates hg hU (upPt z u) (h1 u hu) x hx i).symm

end World

/-! ## The union-find run reads the circuit only at the test points -/

section Congr

variable {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))

theorem trRT_congr {gs gs' : List Gate} (h1 : ∀ u ∈ R, ∀ i, val gs (p u) i = val gs' (p u) i) :
    trRT p R gs = trRT p R gs' := by
  funext i
  unfold trRT
  exact Finset.filter_congr fun u hu => by rw [h1 u hu i]

/-- Two circuits with the same values at `z` and at every test point `p u`, `u ∈ R`, have the
same union-find run (labels and merge wires). -/
theorem run_congr {gs gs' : List Gate} (h0 : ∀ i, val gs z i = val gs' z i)
    (h1 : ∀ u ∈ R, ∀ i, val gs (p u) i = val gs' (p u) i) :
    ∀ k, runLT z p R gs k = runLT z p R gs' k ∧ runMT z p R gs k = runMT z p R gs' k := by
  have ht := trRT_congr p R h1
  have hv : val gs z = val gs' z := funext h0
  have hmg : ∀ l j, MgT z p R gs l j ↔ MgT z p R gs' l j := by
    intro l j
    unfold MgT
    rw [hv, ht]
  have hst : ∀ l j, mstepT z p R gs l j = mstepT z p R gs' l j := by
    intro l j
    unfold mstepT MgT
    simp only [hv, ht]
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hL, hM⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [runLT, hL, hst]
    · simp only [runMT, hL, hM, hmg]

/-- **Merge sets depend only on the values at the test points.** -/
theorem mergeSet_congr {gs gs' : List Gate} (hlen : gs.length = gs'.length)
    (h0 : ∀ i, val gs z i = val gs' z i)
    (h1 : ∀ u ∈ R, ∀ i, val gs (upPt z u) i = val gs' (upPt z u) i) :
    mergeSet gs R z = mergeSet gs' R z := by
  unfold mergeSet
  rw [hlen]
  exact (run_congr z (upPt z) R h0 h1 _).2

end Congr

/-! ## The merge sets of each world -/

section Worlds

variable {n : ℕ} {gates : List Gate}
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

include hg hU

/-- **At a world-0 point, `M_z(R)` is the merge set of the monotone circuit `C0`.** -/
theorem mergeSet_C0_of_world0 (R : Finset (Fin n)) {z : Fin n → Bool} (h0 : World0 gates z) :
    mergeSet gates R z = mergeSet (C0 gates) R z :=
  mergeSet_congr z R (by simp [C0]) (fun i => World0.val_C0 hg hU h0 z le_rfl i)
    (fun u _ i => World0.val_C0 hg hU h0 _ (le_upPt z u) i)

/-- **At a world-1 point, `M_z(R)` is the merge set of the monotone circuit `C1`.** -/
theorem mergeSet_C1_of_world1 {R : Finset (Fin n)} {z : Fin n → Bool} (h1 : World1 gates R z) :
    mergeSet gates R z = mergeSet (C1 gates) R z := by
  rcases R.eq_empty_or_nonempty with hR | ⟨u, hu⟩
  · subst hR
    have a := mergeSet_card_le gates ∅ z
    have b := mergeSet_card_le (C1 gates) ∅ z
    simp only [Finset.card_empty, zero_tsub, nonpos_iff_eq_zero, Finset.card_eq_zero] at a b
    rw [a, b]
  · exact mergeSet_congr z R (by simp [C1])
      (fun i => World1.val_C1 hg hU h1 u hu z (le_upPt z u) i)
      (fun v hv i => World1.val_C1 hg hU h1 v hv _ le_rfl i)

end Worlds

/-! ## The no-mixed fractional target -/

/-- **NoMixedFrac**: `MergeFrac` with every `μ_w` supported on non-mixed zero points. -/
def NoMixedFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∃ μ : Fin m → (Fin n → Bool) → ℝ,
    (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) ∧
    (∀ w z, Mixed gates (S w) z → μ w z = 0) ∧
    (∀ w, ∑ z, μ w z = 1) ∧
    ∀ g : ℕ, ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) ≤ 1

/-- `NoMixedFrac → MergeFrac` (inclusion). -/
theorem mergeFrac_of_noMixedFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (h : NoMixedFrac S gates) : MergeFrac S gates := by
  obtain ⟨μ, h0, hS, -, h1, hl⟩ := h
  exact ⟨μ, h0, hS, h1, hl⟩

open Classical in
/-- **The load of a no-mixed `μ` splits into the two monotone worlds.** The load of a wire is the
`C0` load of the world-0 points plus the `C1` load of the other (world-1) points. -/
theorem noMixed_load_eq {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (μ : Fin m → (Fin n → Bool) → ℝ)
    (hmix : ∀ w z, Mixed gates (S w) z → μ w z = 0) (g : ℕ) :
    ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) =
      ∑ w, ∑ z, (if World0 gates z ∧ g ∈ mergeSet (C0 gates) (S w) z then μ w z else 0) +
        ∑ w, ∑ z, (if ¬ World0 gates z ∧ g ∈ mergeSet (C1 gates) (S w) z then μ w z else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h0 : World0 gates z
  · rw [mergeSet_C0_of_world0 hg hU (S w) h0]
    simp [h0]
  · by_cases h1 : World1 gates (S w) z
    · rw [mergeSet_C1_of_world1 hg hU h1]
      simp [h0]
    · have hz : μ w z = 0 := hmix w z ⟨h0, h1⟩
      simp [hz]

open Classical in
/-- **NoMixedFrac in the two monotone worlds.** A no-mixed `μ` is feasible exactly when, for
every wire, its world-0 load in `C0` plus its world-1 load in `C1` is at most `1`. -/
theorem noMixedFrac_iff {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) :
    NoMixedFrac S gates ↔
      ∃ μ : Fin m → (Fin n → Bool) → ℝ,
        (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) ∧
        (∀ w z, Mixed gates (S w) z → μ w z = 0) ∧
        (∀ w, ∑ z, μ w z = 1) ∧
        ∀ g : ℕ,
          ∑ w, ∑ z, (if World0 gates z ∧ g ∈ mergeSet (C0 gates) (S w) z then μ w z else 0) +
            ∑ w, ∑ z, (if ¬ World0 gates z ∧ g ∈ mergeSet (C1 gates) (S w) z then μ w z else 0)
            ≤ 1 := by
  constructor
  · rintro ⟨μ, h0, hS, hmix, h1, hl⟩
    exact ⟨μ, h0, hS, hmix, h1, fun g => (noMixed_load_eq S hg hU μ hmix g) ▸ hl g⟩
  · rintro ⟨μ, h0, hS, hmix, h1, hl⟩
    exact ⟨μ, h0, hS, hmix, h1, fun g => (noMixed_load_eq S hg hU μ hmix g).symm ▸ hl g⟩

/-! ## The classification in terms of `h` -/

section Hval

variable {n : ℕ} {gates : List Gate} (hU : AtMostOneNot gates) {p : ℕ} (hp : p < gates.length)
  (hN : (gates[p]'hp).op = GateOp.not)

include hU hN

/-- World 0 is `h z = 1`, for `h = hval gates p` the wire read by the NOT gate. -/
theorem world0_iff_hval (z : Fin n → Bool) : World0 gates z ↔ hval gates p z = true := by
  rw [World0, notsAt_iff_of_not hU hp hN, val_not_hval gates p hp hN]
  simp

/-- World 1 of `R` is `h (z + e_u) = 0` for every `u ∈ R`. -/
theorem world1_iff_hval (R : Finset (Fin n)) (z : Fin n → Bool) :
    World1 gates R z ↔ ∀ u ∈ R, hval gates p (upPt z u) = false := by
  unfold World1
  refine forall₂_congr fun u _ => ?_
  rw [notsAt_iff_of_not hU hp hN, val_not_hval gates p hp hN]
  simp

end Hval

end PEqualNP.Outside.L_meta_951_aux
