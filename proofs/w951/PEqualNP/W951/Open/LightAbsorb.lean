import PEqualNP.W951.Open.DDAbsorb

/-!
# LightAbsorb: bottom pay implies light absorption (seat A12)

Board `open-one-not`. Paper: `research/one-not/research/open/A10_light_absorption.md` §1.

* `bottom_F2WitMix`: a wire `0` at the bottom point `canonPt Q` and `1` at two unit atoms is a mixed
  F2 witness (no NOT hypothesis).
* `bottom_zero_of_H0`: with one NOT gate, a wire `0` above `canonPt Q` at a point where `h = 0`
  is `0` at `canonPt Q`.
* `BottomPay` and `lightAbsorb_of_bottomPay`.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Bottom

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

omit hp hg hU hN in
/-- **Bottom witness.** -/
theorem bottom_F2WitMix (S : Fin m → Finset (Fin n)) (w : Fin m) (Q D : Finset (Fin n))
    (hQ : Disjoint Q (S w ∪ D)) (i : ℕ) (hz : val gates (canonPt Q) i = false) {u u' : Fin n}
    (hu : u ∈ S w \ D) (hu' : u' ∈ S w \ D) (huu : u ≠ u')
    (h1 : val gates (upPt (canonPt Q) u) i = true)
    (h2 : val gates (upPt (canonPt Q) u') i = true) :
    MixedSlack.F2WitMix gates (S w) Q D i := by
  refine ⟨canonPt Q, u, u', hu, hu', huu, ?_, fun x hx => canonPt_eq_true.mpr hx, hz, h1, h2⟩
  intro x hx
  have : x ∉ Q := fun hxQ => Finset.disjoint_left.mp hQ hxQ hx
  simp [canonPt, this]

include hg hU hN in
/-- A wire that is `0` at a point `Y ≥ canonPt Q` with `h Y = 0` is `0` at `canonPt Q`. -/
theorem bottom_zero_of_H0 {Q : Finset (Fin n)} {Y : Fin n → Bool} (hle : canonPt Q ≤ Y)
    (hY : hval gates p Y = false) (i : ℕ) (hi : val gates Y i = false) :
    val gates (canonPt Q) i = false := by
  cases h : val gates (canonPt Q) i
  · rfl
  · have := (sign_of_drop gates p hp hg hU hN hle i h hi).2
    rw [hY] at this; exact absurd this (by simp)

open Classical in
/-- **Bottom pay** (hypothesis): disjoint families `E w` of OR gates outside the top family, `0` at
`canonPt Q`, `1` at two unit atoms of `S w \ D`, of the size the light atoms need. -/
def BottomPay (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) : Prop :=
  ∃ E : Fin m → Finset ℕ,
    (∀ a ∈ (aliveSets S Q).filter (DDAt gates p S Q D),
      ∀ b ∈ (aliveSets S Q).filter (DDAt gates p S Q D), a ≠ b → Disjoint (E a) (E b)) ∧
    ∀ w ∈ (aliveSets S Q).filter (DDAt gates p S Q D),
      (S w \ D).card - (heavyAt gates p S Q D w).card -
          (if heavyAt gates p S Q D w = ∅ then 1 else 0) ≤ (E w).card ∧
        ∀ i ∈ E w, i ∈ Finset.Ico n (n + gates.length) ∧ IsOrAt gates (i - n) ∧
          i ∉ (((aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w)).biUnion
                (unitMerge gates S Q D) ∪
              ((aliveSets S Q).filter (DDAt gates p S Q D)).biUnion
                (heavyMerge gates p S Q D)) ∧
          val gates (canonPt Q) i = false ∧
          ∃ u ∈ S w \ D, ∃ u' ∈ S w \ D, u ≠ u' ∧
            val gates (upPt (canonPt Q) u) i = true ∧ val gates (upPt (canonPt Q) u') i = true

/-- **Bottom pay implies light absorption.** -/
theorem lightAbsorb_of_bottomPay (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (hQD : Disjoint Q D) (hB : BottomPay gates p S Q D) : LightAbsorb gates p S Q D := by
  classical
  obtain ⟨E, hdis, hE⟩ := hB
  set DDs := (aliveSets S Q).filter (DDAt gates p S Q D) with hDDs
  have hsub : DDs.biUnion E ⊆ MixedSlack.F2Mix gates S Q D \
      (((aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w)).biUnion
          (unitMerge gates S Q D) ∪ DDs.biUnion (heavyMerge gates p S Q D)) := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨-, hEw⟩ := hE w hw
    obtain ⟨hij, hor, hnot, hz, u, hu, u', hu', huu, h1, h2⟩ := hEw i hiw
    have hwa : w ∈ aliveSets S Q := (Finset.mem_filter.mp hw).1
    have hdisj : Disjoint Q (S w ∪ D) :=
      Finset.disjoint_union_right.mpr ⟨(mem_aliveSets.mp hwa).symm, hQD⟩
    refine Finset.mem_sdiff.mpr ⟨?_, hnot⟩
    simp only [MixedSlack.F2Mix, Finset.mem_filter]
    exact ⟨hij, hor, w, hwa, bottom_F2WitMix gates S w Q D hdisj i hz hu hu' huu h1 h2⟩
  have hcard : ∑ w ∈ DDs, ((S w \ D).card - (heavyAt gates p S Q D w).card -
      (if heavyAt gates p S Q D w = ∅ then 1 else 0)) ≤ (DDs.biUnion E).card := by
    rw [Finset.card_biUnion hdis]
    exact Finset.sum_le_sum fun w hw => (hE w hw).1
  exact hcard.trans (Finset.card_le_card hsub)

end Bottom

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
