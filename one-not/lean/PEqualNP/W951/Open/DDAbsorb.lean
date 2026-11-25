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

open Classical in
/-- **Light absorption** (hypothesis, not a theorem): the light atoms of the DD sets are paid for by
`F2Mix` wires outside the unit merges of non-DD sets and the heavy merges of DD sets. -/
def LightAbsorb (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) : Prop :=
  ∑ w ∈ (aliveSets S Q).filter (DDAt gates p S Q D),
    ((S w \ D).card - (heavyAt gates p S Q D w).card -
      (if heavyAt gates p S Q D w = ∅ then 1 else 0)) ≤
    (MixedSlack.F2Mix gates S Q D \
      (((aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w)).biUnion
          (unitMerge gates S Q D) ∪
        ((aliveSets S Q).filter (DDAt gates p S Q D)).biUnion (heavyMerge gates p S Q D))).card

open Classical in
/-- **DD absorption** (target): the DD sets' `|S w \ D| - 1` is covered by `F2Mix` wires outside the
unit merges of non-DD sets. -/
def DDAbsorb (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) : Prop :=
  ∑ w ∈ (aliveSets S Q).filter (DDAt gates p S Q D), ((S w \ D).card - 1) ≤
    (MixedSlack.F2Mix gates S Q D \
      ((aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w)).biUnion
        (unitMerge gates S Q D)).card

include hg hU hN in
/-- **Light absorption implies DD absorption.** -/
theorem ddAbsorb_of_lightAbsorb (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (hQD : Disjoint Q D) (hov : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hev : ∀ w, ∃ out : ℕ, ∀ x : Fin n → Bool,
      val gates x out = decide (∃ u ∈ S w, x u = true))
    (hL : LightAbsorb gates p S Q D) : DDAbsorb gates p S Q D := by
  classical
  have hdis : ∀ w ∈ aliveSets S Q, Disjoint Q (S w ∪ D) := fun w hw =>
    Finset.disjoint_union_right.mpr ⟨(mem_aliveSets.mp hw).symm, hQD⟩
  set DDs := (aliveSets S Q).filter (DDAt gates p S Q D) with hDDs
  set Ns := (aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w) with hNs
  set N := Ns.biUnion (unitMerge gates S Q D) with hNdef
  set H := DDs.biUnion (heavyMerge gates p S Q D) with hHdef
  have hDDa : ∀ w ∈ DDs, w ∈ aliveSets S Q := fun w hw => (Finset.mem_filter.mp hw).1
  have hNa : ∀ w ∈ Ns, w ∈ aliveSets S Q := fun w hw => (Finset.mem_filter.mp hw).1
  have hHsub : H ⊆ MixedSlack.F2Mix gates S Q D := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨out, hout⟩ := hev w
    exact (heavyMerge_card_ge_and_subset gates p hp hg hU hN S Q D w (hdis w (hDDa w hw)) out
      hout).2 hiw
  have hpair : ∀ a ∈ DDs, ∀ b ∈ DDs, a ≠ b →
      Disjoint (heavyMerge gates p S Q D a) (heavyMerge gates p S Q D b) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨hza, u, hu, u', hu', huu, h1, h2⟩ := heavyMerge_data gates p S Q D a i hia
    obtain ⟨hzb, -⟩ := heavyMerge_data gates p S Q D b i hib
    exact heavy_overlap_false gates p hp hg hU hN S a b (hov a b hab) Q D (hdis b (hDDa b hb)) i
      hzb (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 huu h1 h2
      (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hu').2
  have hHN : Disjoint H N := by
    rw [Finset.disjoint_left]
    intro i hiH hiN
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hiH
    obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp hiN
    have hab : a ≠ b := by
      rintro rfl
      exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
    obtain ⟨-, u, hu, u', hu', huu, h1, h2⟩ := heavyMerge_data gates p S Q D a i hia
    obtain ⟨hzb, -⟩ := unitMerge_data gates S Q D b i hib
    exact heavy_overlap_false gates p hp hg hU hN S a b (hov a b hab) Q D (hdis b (hNa b hb)) i
      hzb (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 huu h1 h2
      (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hu').2
  have hHcard : ∑ w ∈ DDs, ((heavyAt gates p S Q D w).card - 1) ≤ H.card := by
    rw [hHdef, Finset.card_biUnion hpair]
    exact Finset.sum_le_sum fun w hw => by
      obtain ⟨out, hout⟩ := hev w
      exact (heavyMerge_card_ge_and_subset gates p hp hg hU hN S Q D w (hdis w (hDDa w hw)) out
        hout).1
  have hsplit : H.card + (MixedSlack.F2Mix gates S Q D \ (N ∪ H)).card ≤
      (MixedSlack.F2Mix gates S Q D \ N).card := by
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact Finset.mem_sdiff.mpr ⟨hHsub h, fun hN' => Finset.disjoint_left.mp hHN h hN'⟩
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h).1, fun hN' =>
          (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ hN')⟩
    · rw [Finset.disjoint_left]
      intro i hiH hi2
      exact (Finset.mem_sdiff.mp hi2).2 (Finset.mem_union_right _ hiH)
  have hpt : ∀ w ∈ DDs, (S w \ D).card - 1 ≤ ((heavyAt gates p S Q D w).card - 1) +
      ((S w \ D).card - (heavyAt gates p S Q D w).card -
        (if heavyAt gates p S Q D w = ∅ then 1 else 0)) := by
    intro w _
    have hle : (heavyAt gates p S Q D w).card ≤ (S w \ D).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    by_cases h0 : heavyAt gates p S Q D w = ∅
    · rw [h0]; simp
    · have : 1 ≤ (heavyAt gates p S Q D w).card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr h0)
      simp only [h0, ite_false]
      omega
  have hsum : ∑ w ∈ DDs, ((S w \ D).card - 1) ≤ ∑ w ∈ DDs, ((heavyAt gates p S Q D w).card - 1) +
      ∑ w ∈ DDs, ((S w \ D).card - (heavyAt gates p S Q D w).card -
        (if heavyAt gates p S Q D w = ∅ then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  unfold DDAbsorb
  have hL' : ∑ w ∈ DDs, ((S w \ D).card - (heavyAt gates p S Q D w).card -
        (if heavyAt gates p S Q D w = ∅ then 1 else 0)) ≤
      (MixedSlack.F2Mix gates S Q D \ (N ∪ H)).card := hL
  have hfin : ∑ w ∈ DDs, ((S w \ D).card - 1) ≤ (MixedSlack.F2Mix gates S Q D \ N).card := by
    omega
  convert hfin

end Heavy

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
