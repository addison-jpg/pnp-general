import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Lower
import PEqualNP.W951.Main

/-!
# R0' : the core case

`HardCaseCore` = `HardCaseDD4` + every point lying in some set lies in at least two sets of
size `≥ 3`.  `r0_step` (point deletion) is the reduction behind the extra hypothesis
(`MinCE.core`).  `HardCaseCore` is derived from `no_minCE` (`hardCaseCore_of_minCE`) and implies it
(`no_minCE_of_hardCaseCore`, MinCE.lean); `L_meta_951_of_core` is in Final.lean.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The hard case after R0': the DD4 hard case where moreover every point lying in some set
lies in at least two sets of size `≥ 3`. -/
def HardCaseCore : Prop :=
  ∀ {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hhard : ¬ ∀ w, NotQuiet (S w) gates)
    (hz : NotQuiet (Finset.univ : Finset (Fin n)) gates)
    (h1 : ¬ ∃ w0, ∀ w, w ≠ w0 → NotQuiet (S w) gates)
    (hclean : ∀ k j : ℕ, k < gates.length → j < n + k →
      ¬ ∀ x : Fin n → Bool, val gates x (n + k) = val gates x j)
    (hC0 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.or)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hC1 : ¬ ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot GateOp.and)) x (out w) = decide (∃ v ∈ S w, x v = true))
    (hlive : ∀ k : ℕ, k < gates.length → (∃ w, out w = n + k) ∨ ∃ g ∈ gates, (n + k) ∈ g.inputs)
    (hC : ¬ ∃ Q : Fin m → Finset (Fin n), (∀ w, S w ⊆ Q w) ∧
      (∀ w, Good (Q w) (mask (coneOf n gates (out w)) gates)) ∧
      ∀ a b : Fin m, a ≠ b → (S a ∩ Q b).card ≤ 1 ∨ (S b ∩ Q a).card ≤ 1)
    (h1N : ¬ ∃ w0 : Fin m, ∀ w, w ≠ w0 → (∀ (i : ℕ) (hi : i < gates.length),
      i ∈ coneOf n gates (out w) → (gates[i]'hi).op ≠ GateOp.not) ∨ NotQuiet (S w) gates)
    (hlt : gates.length < ∑ i : Fin m, ((S i).card - 1))
    (hDD : ∃ w, val (C1 gates) (Zof (S w)) (out w) = true ∧
      ∃ u ∈ S w, val (C0 gates) (eof u) (out w) = false)
    (h4 : ∃ w, 4 ≤ (S w).card)
    (hcore : ∀ v : Fin n, (∃ w, v ∈ S w) →
      2 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w ∧ 3 ≤ (S w).card).card),
    False

/-- R0 as an induction step: a point `v` lying in some set and in at most one set of size `≥ 3`
can be deleted; the bound follows from the bound for all strictly shorter circuits. -/
theorem r0_step {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List Gate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool),
        val gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (v : Fin n) (hv : ∃ w, v ∈ S w)
    (hbig : (Finset.univ.filter fun w : Fin m => v ∈ S w ∧ 3 ≤ (S w).card).card ≤ 1) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  classical
  set T : Fin m → Finset (Fin n) := fun w => (S w).erase v with hT
  let A := {w : Fin m // 2 ≤ (T w).card}
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hlow := DC_lower S hS gates out hg hev h2 v hbig
  have hdeg : 1 ≤ (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
    obtain ⟨w, hw⟩ := hv
    exact Finset.card_pos.mpr ⟨w, by simp [hw]⟩
  have hpb := promise_bound v gates.length B gates.length (Fintype.card A)
    (fun i => T (e i).1) gates (fun i => out (e i).1) rfl
    (fun i => by simp [hT]) (fun i => (e i).2)
    (fun i j hij => by
      have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
      refine le_trans (Finset.card_le_card ?_) (hS _ _ hne)
      intro t ht
      simp only [hT, Finset.mem_inter, Finset.mem_erase] at ht
      exact Finset.mem_inter.mpr ⟨ht.1.2, ht.2.2⟩)
    hg hU
    (fun i x hx => by
      rw [hev]
      congr 1
      apply propext
      constructor
      · rintro ⟨u, hu, hxu⟩
        refine ⟨u, ?_, hxu⟩
        simp only [hT, Finset.mem_erase]
        exact ⟨fun e' => by rw [e', hx] at hxu; exact absurd hxu (by simp), hu⟩
      · rintro ⟨u, hu, hxu⟩
        exact ⟨u, Finset.mem_of_mem_erase hu, hxu⟩)
    (by omega)
  have h1 : ∀ w, (S w).card - 1 = ((T w).card - 1) + (if v ∈ S w then 1 else 0) := by
    intro w
    by_cases h : v ∈ S w
    · have := h2 w
      simp only [hT, Finset.card_erase_of_mem h, h, if_true]
      omega
    · simp [hT, Finset.erase_eq_of_notMem h, h]
  have h3 : ∑ w : Fin m, ((T w).card - 1) = ∑ i : Fin (Fintype.card A), ((T (e i).1).card - 1) := by
    rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun w : Fin m => 2 ≤ (T w).card)
      (f := fun w => (T w).card - 1) fun w _ hw => by omega]
    exact (PEqualNP.Base.Matching.sum_equivFin_subtype (fun w : Fin m => 2 ≤ (T w).card)
      (fun w => (T w).card - 1)).symm
  have hsum : ∑ w : Fin m, ((S w).card - 1) =
      ∑ i : Fin (Fintype.card A), ((T (e i).1).card - 1) +
        (Finset.univ.filter fun w : Fin m => v ∈ S w).card := by
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_add_distrib, h3, Finset.card_filter]
  omega

end PEqualNP.Outside.L_meta_951_aux
