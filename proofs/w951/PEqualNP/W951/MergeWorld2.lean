import PEqualNP.W951.MergeWorld

/-! MergeWorld2: the refined no-mixed target (gAdyD, board `agents/qg-d2-nomixed.md` item 4; coord
piece after MergeWorld).

`h = hval gates p` is the wire read by the (single) NOT gate at position `p`.
* `HeavySet gates p S`: `h(e_u) = 1` for some `u ∈ S`. A heavy set has no world-1 zero point
  (`HeavySet.not_world1`).
* gAdyD's characterization (`onlyMixed_iff`): every zero point of `S` is mixed exactly when `S`
  is heavy and `h(1_{V ∖ S}) = 0` (`Zof S` is the point that is `1` exactly off `S`).
  Corollary `exists_nonMixed_of_not_heavy`: a set that is not heavy has a non-mixed zero point.
* `RefinedNoMixedFrac`: `MergeFrac` in which heavy sets may use every zero point and the other
  sets only world-0 and world-1 points. `mergeFrac_of_refinedNoMixedFrac`,
  `refinedNoMixedFrac_of_noMixedFrac`.
* Load split (`refined_load_eq`, `refinedNoMixedFrac_iff`): the load of a refined `μ` is the load
  of the heavy sets in the real circuit, plus the `C0` load of the world-0 points of the other
  sets, plus the `C1` load of their world-1 points. The per-set form is
  `world_load_eq_of_noMixed`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Points -/

section Points

variable {n : ℕ}

theorem eof_le_upPt (z : Fin n → Bool) (u : Fin n) : eof u ≤ upPt z u := by
  intro c
  by_cases h : c = u
  · subst h
    simp [upPt]
  · simp [eof, h]

theorem le_Zof {S : Finset (Fin n)} {z : Fin n → Bool} (hz : ∀ v ∈ S, z v = false) :
    z ≤ Zof S := by
  intro c
  by_cases h : c ∈ S
  · simp [hz c h]
  · simp [Zof, h]

theorem Zof_zero (S : Finset (Fin n)) : ∀ v ∈ S, Zof S v = false := by
  intro v hv
  simp [Zof, hv]

theorem upPt_false (u : Fin n) : upPt (fun _ => false) u = eof u := by
  funext c
  by_cases h : c = u
  · subst h
    simp [upPt, eof]
  · simp [upPt, eof, h]

end Points

/-! ## Heavy sets -/

/-- A set `S` is heavy for `h = hval gates p` when `h(e_u) = 1` for some `u ∈ S`. -/
def HeavySet {n : ℕ} (gates : List Gate) (p : ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ u ∈ S, hval gates p (eof u) = true

section OneNot

variable {n : ℕ} {gates : List Gate}
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) {p : ℕ} (hp : p < gates.length)
  (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN

/-- A heavy set has no world-1 point. -/
theorem HeavySet.not_world1 {S : Finset (Fin n)} (hS : HeavySet gates p S) (z : Fin n → Bool) :
    ¬ World1 gates S z := by
  obtain ⟨u, hu, he⟩ := hS
  rw [world1_iff_hval hU hp hN]
  intro h
  have h' := hval_mono gates p hp hg hU hN (eof_le_upPt z u) he
  rw [h u hu] at h'
  exact absurd h' (by simp)

/-- **gAdyD's characterization.** Every zero point of `S` is mixed exactly when `S` is heavy and
`h(1_{V ∖ S}) = 0`. -/
theorem onlyMixed_iff (S : Finset (Fin n)) :
    (∀ z : Fin n → Bool, (∀ v ∈ S, z v = false) → Mixed gates S z) ↔
      HeavySet gates p S ∧ hval gates p (Zof S) = false := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := (h (fun _ => false) (fun _ _ => rfl)).2
      rw [world1_iff_hval hU hp hN] at h1
      push Not at h1
      obtain ⟨u, hu, hv⟩ := h1
      refine ⟨u, hu, ?_⟩
      rw [← upPt_false]
      simpa using hv
    · have h0 := (h (Zof S) (Zof_zero S)).1
      rw [world0_iff_hval hU hp hN] at h0
      simpa using h0
  · rintro ⟨hH, hZ⟩ z hz
    refine ⟨?_, HeavySet.not_world1 hg hU hp hN hH z⟩
    rw [world0_iff_hval hU hp hN]
    intro h1
    have h' := hval_mono gates p hp hg hU hN (le_Zof hz) h1
    rw [hZ] at h'
    exact absurd h' (by simp)

/-- A set that is not heavy has a non-mixed zero point. -/
theorem exists_nonMixed_of_not_heavy {S : Finset (Fin n)} (hS : ¬ HeavySet gates p S) :
    ∃ z : Fin n → Bool, (∀ v ∈ S, z v = false) ∧ ¬ Mixed gates S z := by
  by_contra h
  push Not at h
  exact hS ((onlyMixed_iff hg hU hp hN S).mp h).1

/-- If no set is heavy, every set has a non-mixed zero point. -/
theorem forall_exists_nonMixed {m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ w, ¬ HeavySet gates p (S w)) :
    ∀ w, ∃ z : Fin n → Bool, (∀ v ∈ S w, z v = false) ∧ ¬ Mixed gates (S w) z :=
  fun w => exists_nonMixed_of_not_heavy hg hU hp hN (hS w)

end OneNot

/-! ## The refined target and its load split -/

/-- **RefinedNoMixedFrac**: `MergeFrac` in which a heavy set may use every zero point and every other
set only world-0 and world-1 points. -/
def RefinedNoMixedFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (p : ℕ) :
    Prop :=
  ∃ μ : Fin m → (Fin n → Bool) → ℝ,
    (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) ∧
    (∀ w z, ¬ HeavySet gates p (S w) → Mixed gates (S w) z → μ w z = 0) ∧
    (∀ w, ∑ z, μ w z = 1) ∧
    ∀ g : ℕ, ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) ≤ 1

theorem mergeFrac_of_refinedNoMixedFrac {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (p : ℕ) (h : RefinedNoMixedFrac S gates p) : MergeFrac S gates := by
  obtain ⟨μ, h0, hS, -, h1, hl⟩ := h
  exact ⟨μ, h0, hS, h1, hl⟩

theorem refinedNoMixedFrac_of_noMixedFrac {n m : ℕ} (S : Fin m → Finset (Fin n))
    (gates : List Gate) (p : ℕ) (h : NoMixedFrac S gates) : RefinedNoMixedFrac S gates p := by
  obtain ⟨μ, h0, hS, hmix, h1, hl⟩ := h
  exact ⟨μ, h0, hS, fun w z _ hz => hmix w z hz, h1, hl⟩

open Classical in
/-- **Per-set load split.** For a weighting `ν` of the zero points of `R` that vanishes on mixed
points, the load of a wire is its `C0` load on world-0 points plus its `C1` load on the others. -/
theorem world_load_eq_of_noMixed {n : ℕ} {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (R : Finset (Fin n)) (ν : (Fin n → Bool) → ℝ)
    (hmix : ∀ z, Mixed gates R z → ν z = 0) (g : ℕ) :
    ∑ z, (if g ∈ mergeSet gates R z then ν z else 0) =
      ∑ z, (if World0 gates z ∧ g ∈ mergeSet (C0 gates) R z then ν z else 0) +
        ∑ z, (if ¬ World0 gates z ∧ g ∈ mergeSet (C1 gates) R z then ν z else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h0 : World0 gates z
  · rw [mergeSet_C0_of_world0 hg hU R h0]
    simp [h0]
  · by_cases h1 : World1 gates R z
    · rw [mergeSet_C1_of_world1 hg hU h1]
      simp [h0]
    · have hz : ν z = 0 := hmix z ⟨h0, h1⟩
      simp [hz]

open Classical in
/-- **Refined load split.** For a refined `μ`, the load of a wire is the load of the heavy sets in
the real circuit, plus the `C0` load of the world-0 points of the other sets, plus the `C1` load of
their world-1 points. -/
theorem refined_load_eq {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (p : ℕ) (μ : Fin m → (Fin n → Bool) → ℝ)
    (hmix : ∀ w z, ¬ HeavySet gates p (S w) → Mixed gates (S w) z → μ w z = 0) (g : ℕ) :
    ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) =
      ∑ w ∈ Finset.univ.filter (fun w => HeavySet gates p (S w)),
          ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) +
        (∑ w ∈ Finset.univ.filter (fun w => ¬ HeavySet gates p (S w)),
            ∑ z, (if World0 gates z ∧ g ∈ mergeSet (C0 gates) (S w) z then μ w z else 0) +
          ∑ w ∈ Finset.univ.filter (fun w => ¬ HeavySet gates p (S w)),
            ∑ z, (if ¬ World0 gates z ∧ g ∈ mergeSet (C1 gates) (S w) z then μ w z else 0)) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => HeavySet gates p (S w))
    (fun w => ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0)), ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w hw => ?_
  exact world_load_eq_of_noMixed hg hU (S w) (μ w)
    (fun z hz => hmix w z (Finset.mem_filter.mp hw).2 hz) g

open Classical in
/-- **RefinedNoMixedFrac in the split form.** -/
theorem refinedNoMixedFrac_iff {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (p : ℕ) :
    RefinedNoMixedFrac S gates p ↔
      ∃ μ : Fin m → (Fin n → Bool) → ℝ,
        (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) ∧
        (∀ w z, ¬ HeavySet gates p (S w) → Mixed gates (S w) z → μ w z = 0) ∧
        (∀ w, ∑ z, μ w z = 1) ∧
        ∀ g : ℕ,
          ∑ w ∈ Finset.univ.filter (fun w => HeavySet gates p (S w)),
              ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) +
            (∑ w ∈ Finset.univ.filter (fun w => ¬ HeavySet gates p (S w)),
                ∑ z, (if World0 gates z ∧ g ∈ mergeSet (C0 gates) (S w) z then μ w z else 0) +
              ∑ w ∈ Finset.univ.filter (fun w => ¬ HeavySet gates p (S w)),
                ∑ z, (if ¬ World0 gates z ∧ g ∈ mergeSet (C1 gates) (S w) z then μ w z else 0))
            ≤ 1 := by
  constructor
  · rintro ⟨μ, h0, hS, hmix, h1, hl⟩
    exact ⟨μ, h0, hS, hmix, h1, fun g => (refined_load_eq S hg hU p μ hmix g) ▸ hl g⟩
  · rintro ⟨μ, h0, hS, hmix, h1, hl⟩
    exact ⟨μ, h0, hS, hmix, h1, fun g => (refined_load_eq S hg hU p μ hmix g).symm ▸ hl g⟩

end PEqualNP.Outside.L_meta_951_aux
