import PEqualNP.W951.MergeWorld

/-!
# Cross-world gates (the objects of the missing piece of `no_minCE`)

Coord assignment (reset 2026-11-24). A wire `g` is a CROSS-WORLD gate (`CrossWorldAt`) when it is a
merge gate of a set `a` at a world-0 zero point `z` of `S a` (`h z = 1`) and a merge gate of a set
`b ≠ a` at a world-1 zero point `z'` of `S b` (`h (z' + e_u) = 0` for every `u ∈ S b`); merge sets
are `mergeSet` (MergeFrac), worlds are `World0` / `World1` (MergeWorld). `g` is N-DEPENDENT
(`NDep`) when its `C0` and `C1` values differ as functions.

S1(g) (front, w9/s_fable.md) says that a gate in a world-1 class and in a world-0 class `H_z'(w')`
is N-dependent. For merge sets this needs two extra hypotheses, and both are necessary:
* (i)  `z'` also vanishes on `S a`;
* (ii) `C0(g)` is `0` at `Zof (S a)` (the canonical zero point of `a`).
Under (i) and (ii) the gate is N-dependent (`ndep_of_world1_merge`, `CrossWorldAt.ndep`); (ii)
holds automatically at the canonical world-0 point `z = Zof (S a)` (`CrossWorldAt.ndep_canonical`)
and whenever `C0(g) ≤ OR (S a)` on the up-cube of `z`, front's class `H_z(a)` (`strict_of_cube`).
Without (ii), or without (i), the statement is false: `cx1` and `cx2` are correct circuits (all
problem hypotheses of 951 except `hlt`) with an N-independent cross-world gate; `cx1` satisfies
(i) and `cx2` satisfies (ii).

Proof of the positive part: if `C0(g) = C1(g) = f`, the world-1 merge gives two units `u ≠ u'` of
`S b` with `f (z' + e_u) = 1`; one of them, `v`, avoids `S a`, so `z' + e_v ≤ Zof (S a)` by (i),
and `f (Zof (S a)) = 1` by monotonicity of `C0`, contradicting (ii).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- `g` is N-dependent: its values in `C0` (NOT := 0) and `C1` (NOT := 1) differ somewhere. -/
def NDep (n : ℕ) (gates : List Gate) (g : ℕ) : Prop :=
  ∃ x : Fin n → Bool, val (C0 gates) x g ≠ val (C1 gates) x g

/-- `g` is a cross-world gate for the ordered pair `(a, b)`: a merge gate of `a` at the world-0
zero point `z` of `S a`, and a merge gate of `b ≠ a` at the world-1 zero point `z'` of `S b`. -/
def CrossWorldAt {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (g : ℕ) (a b : Fin m)
    (z z' : Fin n → Bool) : Prop :=
  a ≠ b ∧
    ((∀ v ∈ S a, z v = false) ∧ World0 gates z ∧ g ∈ mergeSet gates (S a) z) ∧
    ((∀ v ∈ S b, z' v = false) ∧ World1 gates (S b) z' ∧ g ∈ mergeSet gates (S b) z')

/-- `g` is a cross-world gate (for some pair of sets and zero points). -/
def CrossWorld {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (g : ℕ) : Prop :=
  ∃ a b z z', CrossWorldAt S gates g a b z z'

/-! ## Merge gates: `0` at `z`, `1` at two test points -/

section Merge

variable {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool)

/-- A merge gate of `R` at `z` is `0` at `z`. -/
theorem val_zero_of_mem_mergeSet {g : ℕ} (hm : g ∈ mergeSet gates R z) :
    val gates z g = false := by
  unfold mergeSet at hm
  obtain ⟨j, -, rfl, hM⟩ := (runMT_mem z (upPt z) R gates _ _).mp hm
  exact hM.1

/-- A merge gate of `R` at `z` is `1` at two test points `z + e_u`, `z + e_u'`, `u ≠ u'` in `R`. -/
theorem two_tests_of_mem_mergeSet {g : ℕ} (hm : g ∈ mergeSet gates R z) :
    ∃ u ∈ R, ∃ u' ∈ R, u ≠ u' ∧ val gates (upPt z u) g = true ∧
      val gates (upPt z u') g = true := by
  classical
  unfold mergeSet at hm
  obtain ⟨j, -, rfl, hM⟩ := (runMT_mem z (upPt z) R gates _ _).mp hm
  have h2 : 1 < (trRT (upPt z) R gates (n + j)).card :=
    lt_of_lt_of_le hM.2 Finset.card_image_le
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp h2
  simp only [trRT, Finset.mem_filter] at hu hu'
  exact ⟨u, hu.1, u', hu'.1, hne, hu.2, hu'.2⟩

end Merge

/-! ## S1(g) for merge sets, with the two extra hypotheses -/

section S1

variable {n m : ℕ} (S : Fin m → Finset (Fin n))
  (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
  {gates : List Gate}
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

include hg in
/-- `C0` is monotone. -/
theorem C0_mono (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true) (i : ℕ)
    (hx : val (C0 gates) x i = true) : val (C0 gates) y i = true :=
  mono_val (C0 gates) (fun g hm => (constNot_mono GateOp.or (Or.inr rfl) gates hg g hm).1)
    x y hxy i hx

include hS hg hU in
/-- **S1(g), core.** A merge gate `g` of `b` at a world-1 point `z'` with `C0(g) = C1(g)` is `1`
at `Zof (S a)` in `C0`, for every set `a ≠ b` whose points `z'` avoids. Contrapositive: (i) and
(ii) make `g` N-dependent. -/
theorem ndep_of_world1_merge (a b : Fin m) (hab : a ≠ b) (z' : Fin n → Bool) (g : ℕ)
    (h1 : World1 gates (S b) z') (hm : g ∈ mergeSet gates (S b) z')
    (hz'a : ∀ v ∈ S a, z' v = false)
    (hstrict : val (C0 gates) (Zof (S a)) g = false) : NDep n gates g := by
  classical
  by_contra hnd
  have heq : ∀ x : Fin n → Bool, val (C0 gates) x g = val (C1 gates) x g := by
    intro x
    by_contra hne
    exact hnd ⟨x, hne⟩
  obtain ⟨u, hu, u', hu', hne, e1, e2⟩ := two_tests_of_mem_mergeSet gates (S b) z' hm
  -- one of the two test units avoids `S a`
  have hv : ∃ v ∈ S b, v ∉ S a ∧ val gates (upPt z' v) g = true := by
    by_cases hua : u ∈ S a
    · by_cases hu'a : u' ∈ S a
      · exfalso
        have hsub : ({u, u'} : Finset (Fin n)) ⊆ S a ∩ S b := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> simp [*]
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at hc
        have := hS a b hab
        omega
      · exact ⟨u', hu', hu'a, e2⟩
    · exact ⟨u, hu, hua, e1⟩
  obtain ⟨v, hvb, hva, hval⟩ := hv
  -- in world 1 the real value at a test point is the `C1` value, which is the `C0` value
  have hC1 : val (C1 gates) (upPt z' v) g = true := by
    rw [← World1.val_C1 hg hU h1 v hvb (upPt z' v) le_rfl g]
    exact hval
  have hC0 : val (C0 gates) (upPt z' v) g = true := by rw [heq]; exact hC1
  -- `z' + e_v ≤ Zof (S a)`
  have hle : ∀ c, upPt z' v c = true → Zof (S a) c = true := by
    intro c hc
    simp only [Zof, decide_eq_true_eq]
    intro hca
    by_cases hcv : c = v
    · subst hcv; exact hva hca
    · rw [upPt, Function.update_of_ne hcv] at hc
      rw [hz'a c hca] at hc
      exact absurd hc (by simp)
  have := C0_mono hg _ _ hle g hC0
  rw [hstrict] at this
  exact absurd this (by simp)

include hS hg hU in
/-- **S1(g) for merge sets.** A cross-world gate is N-dependent when (i) `z'` vanishes on `S a`
and (ii) `C0(g)` is `0` at `Zof (S a)`. -/
theorem CrossWorldAt.ndep {a b : Fin m} {z z' : Fin n → Bool} {g : ℕ}
    (h : CrossWorldAt S gates g a b z z') (hz'a : ∀ v ∈ S a, z' v = false)
    (hstrict : val (C0 gates) (Zof (S a)) g = false) : NDep n gates g :=
  ndep_of_world1_merge S hS hg hU a b h.1 z' g h.2.2.2.1 h.2.2.2.2 hz'a hstrict

include hg hU in
/-- At the canonical world-0 point `z = Zof (S a)` (a hard set), hypothesis (ii) holds. -/
theorem strict_of_canonical {a : Fin m} {g : ℕ} (h0 : World0 gates (Zof (S a)))
    (hm : g ∈ mergeSet gates (S a) (Zof (S a))) : val (C0 gates) (Zof (S a)) g = false := by
  rw [← World0.val_C0 hg hU h0 (Zof (S a)) le_rfl g]
  exact val_zero_of_mem_mergeSet gates (S a) (Zof (S a)) hm

include hS hg hU in
/-- **S1(g) at the canonical world-0 point.** A cross-world gate with `z = Zof (S a)` is
N-dependent when `z'` vanishes on `S a`. -/
theorem CrossWorldAt.ndep_canonical {a b : Fin m} {z' : Fin n → Bool} {g : ℕ}
    (h : CrossWorldAt S gates g a b (Zof (S a)) z') (hz'a : ∀ v ∈ S a, z' v = false) :
    NDep n gates g :=
  h.ndep S hS hg hU hz'a (strict_of_canonical S hg hU h.2.1.2.1 h.2.1.2.2)

/-- Front's world-0 class `H_z(a)` condition (`C0(g) ≤ OR (S a)` on the up-cube of `z`, with `z`
vanishing on `S a`) gives hypothesis (ii). -/
theorem strict_of_cube {a : Fin m} {z : Fin n → Bool} {g : ℕ} (hza : ∀ v ∈ S a, z v = false)
    (hcube : ∀ x : Fin n → Bool, z ≤ x → val (C0 gates) x g = true → ∃ v ∈ S a, x v = true) :
    val (C0 gates) (Zof (S a)) g = false := by
  by_contra hne
  have hle : z ≤ Zof (S a) := by
    intro c
    by_cases hc : c ∈ S a
    · rw [hza c hc]; exact Bool.false_le _
    · simp [Zof, hc]
  obtain ⟨v, hv, hxv⟩ := hcube _ hle (by simpa using hne)
  simp [Zof, hv] at hxv

end S1

/-! ## Both extra hypotheses are necessary -/

/-- `cx1`: `x0 ∨ x2`, `x1 ∨ x3`, `f = g5 ∨ g6`, `¬ x4`, outputs `x0 ∨ x1`, `x2 ∨ x3`. -/
def cx1Gates : List Gate :=
  [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩]

/-- `cx2`: `P = x0 ∧ (x2 ∨ x4)`, `Q = (x1 ∧ x4) ∨ (x0 ∧ x3)`, `f = P ∨ Q`, `¬ x4`, outputs. -/
def cx2Gates : List Gate :=
  [⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [0, 3]⟩,
    ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩]

/-- The sets of both examples: `S 0 = {0, 1}`, `S 1 = {2, 3}` (`n = 5`; the NOT reads `x4`). -/
def cxS : Fin 2 → Finset (Fin 5) := ![{0, 1}, {2, 3}]

/-- The point `e4`. -/
def cxE4 : Fin 5 → Bool := fun i => decide (i = 4)

/-- The point `e0`. -/
def cxE0 : Fin 5 → Bool := fun i => decide (i = 0)

/-- The problem hypotheses of 951 (`IsCE` without `hlt`). -/
structure ProblemHyps {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) : Prop where
  h2 : ∀ i : Fin m, 2 ≤ (S i).card
  hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1
  hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
  hU : AtMostOneNot gates
  hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)

theorem cxS_h2 : ∀ i : Fin 2, 2 ≤ (cxS i).card := by decide

theorem cxS_hS : ∀ i j : Fin 2, i ≠ j → (cxS i ∩ cxS j).card ≤ 1 := by decide

set_option maxRecDepth 10000 in
theorem cx1_hyps : ProblemHyps cxS cx1Gates ![9, 10] := by
  refine ⟨cxS_h2, cxS_hS, ?_, ?_, by decide⟩
  · intro g hg
    simp only [cx1Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i1 i2 h1 h2 e1 e2
    simp only [cx1Gates, List.length_cons, List.length_nil] at h1 h2
    interval_cases i1 <;> interval_cases i2 <;> simp_all [cx1Gates]

set_option maxRecDepth 10000 in
theorem cx2_hyps : ProblemHyps cxS cx2Gates ![12, 13] := by
  refine ⟨cxS_h2, cxS_hS, ?_, ?_, by decide⟩
  · intro g hg
    simp only [cx2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i1 i2 h1 h2 e1 e2
    simp only [cx2Gates, List.length_cons, List.length_nil] at h1 h2
    interval_cases i1 <;> interval_cases i2 <;> simp_all [cx2Gates]

set_option maxRecDepth 10000 in
/-- **(ii) is necessary.** In `cx1`, wire `7` (`f = (x0 ∨ x2) ∨ (x1 ∨ x3)`) is a cross-world gate
(`a = 0` at the world-0 point `e4`, `b = 1` at the world-1 point `0`), `z' = 0` vanishes on `S a`
(hypothesis (i)), and `f` is N-independent. -/
theorem cx1_counterexample :
    ProblemHyps cxS cx1Gates ![9, 10] ∧ CrossWorldAt cxS cx1Gates 7 0 1 cxE4 (fun _ => false) ∧
      (∀ v ∈ cxS 0, (fun _ : Fin 5 => false) v = false) ∧ ¬ NDep 5 cx1Gates 7 := by
  refine ⟨cx1_hyps, ⟨by decide, ⟨by decide, ?_, by decide⟩, ⟨by decide, ?_, by decide⟩⟩,
    by decide, ?_⟩
  · intro p hp hn
    simp only [cx1Gates, List.length_cons, List.length_nil] at hp
    interval_cases p <;> decide
  · intro u hu p hp hn
    simp only [cx1Gates, List.length_cons, List.length_nil] at hp
    have hu' : u = 2 ∨ u = 3 := by simpa [cxS] using hu
    rcases hu' with rfl | rfl <;> interval_cases p <;> first | decide | simp [cx1Gates] at hn
  · rintro ⟨x, hx⟩
    revert x
    decide

set_option maxRecDepth 10000 in
/-- **(i) is necessary.** In `cx2`, wire `10` (`f = (x0 ∧ (x2 ∨ x4)) ∨ ((x1 ∧ x4) ∨ (x0 ∧ x3))`)
is a cross-world gate (`a = 0` at the world-0 point `e4`, `b = 1` at the world-1 point `e0`),
`C0(f)` is `0` at `Zof (S a)` (hypothesis (ii)), and `f` is N-independent; `z' = e0` meets `S a`. -/
theorem cx2_counterexample :
    ProblemHyps cxS cx2Gates ![12, 13] ∧ CrossWorldAt cxS cx2Gates 10 0 1 cxE4 cxE0 ∧
      val (C0 cx2Gates) (Zof (cxS 0)) 10 = false ∧ ¬ NDep 5 cx2Gates 10 := by
  refine ⟨cx2_hyps, ⟨by decide, ⟨by decide, ?_, by decide⟩, ⟨by decide, ?_, by decide⟩⟩,
    by decide, ?_⟩
  · intro p hp hn
    simp only [cx2Gates, List.length_cons, List.length_nil] at hp
    interval_cases p <;> first | decide | simp [cx2Gates] at hn
  · intro u hu p hp hn
    simp only [cx2Gates, List.length_cons, List.length_nil] at hp
    have hu' : u = 2 ∨ u = 3 := by simpa [cxS] using hu
    rcases hu' with rfl | rfl <;> interval_cases p <;> first | decide | simp [cx2Gates] at hn
  · rintro ⟨x, hx⟩
    revert x
    decide

end PEqualNP.Outside.L_meta_951_aux
