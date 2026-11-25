import PEqualNP.W951.Open.F2TransferRun

/-!
# DDAbsorb: heavy merges of a DD set (seat A9)

Board `open-one-not`. Paper: `one-not/research/open/A7_dd_absorption.md` §1(a,b).

* `heavy_overlap_false`: two heavy points (`h = 1` at the unit atom) of `S a \ D` cannot both raise a
  wire that is `0` at the top zero point of `S b ∪ D` (`|S a ∩ S b| ≤ 1`).
* `heavyMerge_card_ge_and_subset`: the unit-form merge run over only the heavy points of `S w \ D`
  has at least `|heavy| - 1` wires and lies in `F2Mix`, with no DD hypothesis.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Heavy

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **Heavy points cannot overlap.** -/
theorem heavy_overlap_false (S : Fin m → Finset (Fin n)) (a b : Fin m)
    (hab : (S a ∩ S b).card ≤ 1) (Q D : Finset (Fin n)) (hQ : Disjoint Q (S b ∪ D)) (i : ℕ)
    (hz : val gates (Zof (S b ∪ D)) i = false) {u u' : Fin n} (hu : u ∈ S a \ D)
    (hu' : u' ∈ S a \ D) (huu : u ≠ u') (h1 : val gates (upPt (canonPt Q) u) i = true)
    (h2 : val gates (upPt (canonPt Q) u') i = true)
    (hh1 : hval gates p (upPt (canonPt Q) u) = true)
    (hh2 : hval gates p (upPt (canonPt Q) u') = true) : False := by
  by_cases huB : u ∈ S b
  · by_cases hu'B : u' ∈ S b
    · have : 2 ≤ (S a ∩ S b).card :=
        Finset.one_lt_card.mpr ⟨u, mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1, huB⟩, u',
          mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu').1, hu'B⟩, huu⟩
      omega
    · have hle := unit_le_top hQ (u := u') (by
        simp [hu'B, (Finset.mem_sdiff.mp hu').2])
      have := (sign_of_drop gates p hp hg hU hN hle i h2 hz).1
      rw [hh2] at this; exact absurd this (by simp)
  · have hle := unit_le_top hQ (u := u) (by simp [huB, (Finset.mem_sdiff.mp hu).2])
    have := (sign_of_drop gates p hp hg hU hN hle i h1 hz).1
    rw [hh1] at this; exact absurd this (by simp)

open Classical in
/-- The heavy points of `S w \ D` at `(Q, D)`: `h = 1` at the unit atom. -/
noncomputable def heavyAt (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) :
    Finset (Fin n) :=
  (S w \ D).filter (fun u => hval gates p (upPt (canonPt Q) u) = true)

/-- The merge set of the unit-form run over the heavy points of `w`. -/
noncomputable def heavyMerge (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) :
    Finset ℕ :=
  runMT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w) gates gates.length

omit hp hg hU hN in
/-- Data carried by a wire of a heavy merge set. -/
theorem heavyMerge_data (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) (i : ℕ)
    (hi : i ∈ heavyMerge gates p S Q D w) :
    val gates (Zof (S w ∪ D)) i = false ∧ ∃ u ∈ heavyAt gates p S Q D w,
      ∃ u' ∈ heavyAt gates p S Q D w, u ≠ u' ∧
      val gates (upPt (canonPt Q) u) i = true ∧ val gates (upPt (canonPt Q) u') i = true := by
  classical
  obtain ⟨j, -, rfl, -⟩ :=
    (runMT_mem (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w) gates
      gates.length _).mp hi
  obtain ⟨⟨u, hu, u', hu', h1, h2, hne⟩, -⟩ :=
    run_recordT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w) gates
      gates.length j hi
  have h0 : val gates (Zof (S w ∪ D)) (n + j) = false := by
    have h := run_sub_DT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w)
      gates _ hi
    simp only [DT, Finset.mem_filter] at h
    exact h.2.1
  exact ⟨h0, u, hu, u', hu', fun h => hne (h ▸ rfl), h1, h2⟩

include hg hU hN in
/-- **Heavy merges of any alive set** (DD or not): at least `|heavy| - 1` wires, all in `F2Mix`. -/
theorem heavyMerge_card_ge_and_subset (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (w : Fin m) (hw : Disjoint Q (S w ∪ D)) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x out = decide (∃ u ∈ S w, x u = true)) :
    (heavyAt gates p S Q D w).card - 1 ≤ (heavyMerge gates p S Q D w).card ∧
      heavyMerge gates p S Q D w ⊆ MixedSlack.F2Mix gates S Q D := by
  classical
  have hwa : w ∈ aliveSets S Q :=
    mem_aliveSets.mpr (Finset.disjoint_of_subset_left Finset.subset_union_left hw.symm)
  have hsub : heavyAt gates p S Q D w ⊆ S w \ D := Finset.filter_subset _ _
  have hT : ∀ u ∈ heavyAt gates p S Q D w, ∀ c : Fin n, upPt (canonPt Q) u c = true →
      Zof (S w ∪ D) c = false → c = u := fun u hu =>
    unit_testSystem (R := S w) (D := D) hw u (hsub hu)
  have hall : ∀ u ∈ heavyAt gates p S Q D w, hval gates p (upPt (canonPt Q) u) = true :=
    fun u hu => (Finset.mem_filter.mp hu).2
  have hgood := goodT_of_noDD gates p hp hg hU hN (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u)
    (heavyAt gates p S Q D w) (Or.inr hall)
  have hzero : ∀ x ∈ S w, Zof (S w ∪ D) x = false := by
    intro x hx
    simp [Zof, hx]
  refine ⟨?_, ?_⟩
  · refine merge_countT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w)
      gates hT hgood out ?_ fun u hu => ?_
    · rw [hev]
      simpa using fun y hy => hzero y hy
    · rw [hev]
      exact decide_eq_true ⟨u, (Finset.mem_sdiff.mp (hsub hu)).1, by simp [upPt]⟩
  · intro i hi
    obtain ⟨j, -, rfl, -⟩ :=
      (runMT_mem (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (heavyAt gates p S Q D w) gates
        gates.length i).mp hi
    obtain ⟨hjl, hor⟩ := runMT_or gates hg (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u)
      (heavyAt gates p S Q D w) hT hgood j hi
    obtain ⟨h0, u, hu, u', hu', huu, h1, h2⟩ := heavyMerge_data gates p S Q D w _ hi
    have hij : n + j ∈ Finset.Ico n (n + gates.length) := by
      rw [Finset.mem_Ico]; omega
    simp only [MixedSlack.F2Mix, Finset.mem_filter]
    refine ⟨hij, ?_, w, hwa, ?_⟩
    · show IsOrAt gates (n + j - n)
      rw [Nat.add_sub_cancel_left]
      exact ⟨gates[j], List.getElem?_eq_getElem hjl, hor⟩
    have hup : ∀ t ∈ heavyAt gates p S Q D w, val gates (upPt (canonPt Q) t) (n + j) = true →
        val gates (Function.update (Zof (S w ∪ D)) t true) (n + j) = true := by
      intro t ht h
      cases h' : val gates (Function.update (Zof (S w ∪ D)) t true) (n + j)
      · have := (sign_of_drop gates p hp hg hU hN (upPt_le_upPt (canonPt_le_top hw) t) (n + j)
          h h').1
        rw [hall t ht] at this; exact absurd this (by simp)
      · rfl
    refine ⟨Zof (S w ∪ D), u, u', hsub hu, hsub hu', huu, ?_, ?_, h0, hup u hu h1,
      hup u' hu' h2⟩
    · intro x hx
      simp [Zof, hx]
    intro x hx
    have : x ∉ S w ∪ D := Finset.disjoint_left.mp hw hx
    simp [Zof, this]

end Heavy

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
