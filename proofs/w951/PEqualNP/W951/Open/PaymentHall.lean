import PEqualNP.W951.Open.LightAbsorb

/-!
# PaymentHall as a Prop (seat S1)

Board `open-one-not`. Paper: `research/one-not/research/open/U1_unify.md` §1 (the payment Hall condition) and
§2.1 (BottomPay = PHC at the point `1_Q`).

* `PaymentHall W E need Φ`: a finite set `E` of payers, a family `W` of sets, per set and payer a
  hyperedge `Φ w g` on the classes of `w`; there are pairwise disjoint sets `F w ⊆ E` of size
  `need w`, each payer of `F w` picking two distinct classes of its hyperedge, the picked pairs
  distinct and forming a forest (acyclic graph) on the classes.
* `card_ge_of_paymentHall`: `∑ need ≤ |E|`.
* `bottomPay_of_paymentHall`: `BottomPay` is the instance at `canonPt Q` (heavy atoms joined into
  the class `none`, light atoms singletons `some u`).

This file only states PHC and proves these two reductions; PHC itself is not proved here.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Generic

variable {ι α γ : Type*} [DecidableEq α] [DecidableEq γ]

/-- **Payment Hall condition.** -/
def PaymentHall (W : Finset ι) (E : Finset α) (need : ι → ℕ) (Φ : ι → α → Finset γ) : Prop :=
  ∃ (F : ι → Finset α) (pick : ι → α → γ × γ),
    (∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (F a) (F b)) ∧
    ∀ w ∈ W, F w ⊆ E ∧ (F w).card = need w ∧
      (∀ g ∈ F w, (pick w g).1 ∈ Φ w g ∧ (pick w g).2 ∈ Φ w g ∧ (pick w g).1 ≠ (pick w g).2) ∧
      Set.InjOn (fun g => s((pick w g).1, (pick w g).2)) (F w : Set α) ∧
      (SimpleGraph.fromEdgeSet
        (((F w).image (fun g => s((pick w g).1, (pick w g).2)) : Finset (Sym2 γ)) :
          Set (Sym2 γ))).IsAcyclic

/-- **Counting.** The needs of all sets are paid by distinct payers. -/
theorem card_ge_of_paymentHall {W : Finset ι} {E : Finset α} {need : ι → ℕ}
    {Φ : ι → α → Finset γ} (h : PaymentHall W E need Φ) : ∑ w ∈ W, need w ≤ E.card := by
  obtain ⟨F, pick, hdis, hF⟩ := h
  calc ∑ w ∈ W, need w = ∑ w ∈ W, (F w).card :=
        Finset.sum_congr rfl fun w hw => ((hF w hw).2.1).symm
    _ = (W.biUnion F).card := (Finset.card_biUnion hdis).symm
    _ ≤ E.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun w hw => (hF w hw).1)

end Generic

section Bottom

open Classical

variable {n m : ℕ} (gates : List Gate) (p : ℕ)

/-- Class of an atom at `w`: heavy atoms are joined into `none`, light atoms are singletons. -/
noncomputable def bottomCls (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m)
    (u : Fin n) : Option (Fin n) :=
  if u ∈ heavyAt gates p S Q D w then none else some u

/-- The hyperedge of payer `g` at `w`: classes of the atoms `u ∈ S w \ D` with `g = 1` at
`canonPt Q + e_u`. -/
noncomputable def bottomΦ (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m)
    (g : ℕ) : Finset (Option (Fin n)) :=
  ((S w \ D).filter (fun u => val gates (upPt (canonPt Q) u) g = true)).image
    (bottomCls gates p S Q D w)

/-- The payers: OR gates outside the top family, `0` at `canonPt Q`. -/
noncomputable def bottomPayers (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter (fun i =>
    IsOrAt gates (i - n) ∧
    i ∉ (((aliveSets S Q).filter (fun w => ¬ DDAt gates p S Q D w)).biUnion
            (unitMerge gates S Q D) ∪
          ((aliveSets S Q).filter (DDAt gates p S Q D)).biUnion (heavyMerge gates p S Q D)) ∧
    val gates (canonPt Q) i = false)

/-- The need of a DD set: number of classes minus one. -/
noncomputable def bottomNeed (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) : ℕ :=
  (S w \ D).card - (heavyAt gates p S Q D w).card -
    (if heavyAt gates p S Q D w = ∅ then 1 else 0)

/-- **BottomPay is PHC at `1_Q`.** -/
theorem bottomPay_of_paymentHall (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n))
    (h : PaymentHall ((aliveSets S Q).filter (DDAt gates p S Q D))
      (bottomPayers gates p S Q D) (bottomNeed gates p S Q D)
      (bottomΦ gates p S Q D)) :
    BottomPay gates p S Q D := by
  obtain ⟨F, pick, hdis, hF⟩ := h
  refine ⟨F, hdis, fun w hw => ?_⟩
  obtain ⟨hsub, hcard, hpick, -, -⟩ := hF w hw
  refine ⟨hcard.ge, fun i hi => ?_⟩
  have hi' := Finset.mem_filter.mp (hsub hi)
  have hij := (Finset.mem_filter.mp (hsub hi)).1
  have hor := hi'.2.1
  have hnot := hi'.2.2.1
  have hz := hi'.2.2.2
  have h1 := (hpick i hi).1
  have h2 := (hpick i hi).2.1
  have h12 := (hpick i hi).2.2
  obtain ⟨u, hu, hcu⟩ := Finset.mem_image.mp h1
  obtain ⟨u', hu', hcu'⟩ := Finset.mem_image.mp h2
  have hu1 := Finset.mem_filter.mp hu
  have hu2 := Finset.mem_filter.mp hu'
  have huu : u ≠ u' := by
    rintro rfl
    exact h12 (hcu.symm.trans hcu')
  exact ⟨hij, hor, hnot, hz, u, hu1.1, u', hu2.1, huu, hu1.2, hu2.2⟩

end Bottom

end PEqualNP.Outside.L_meta_951_aux.F2Transfer

#print axioms PEqualNP.Outside.L_meta_951_aux.F2Transfer.card_ge_of_paymentHall
#print axioms PEqualNP.Outside.L_meta_951_aux.F2Transfer.bottomPay_of_paymentHall
