import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PairLemma

/-!
# Heredity (pairrule_log.md §0)

From a circuit for `F - b` (the sets `S i \ {b}`) one gets a circuit for `F` by adding one gate
`o_S := o_{S-b} ∨ x_b` per set `S ∋ b` with `|S| ≥ 2` (for `S = {b}` the output is the wire `x_b`,
no gate).  The number of added gates is `base(F) - base(F - b)` (`= deg b` when all `|S| ≥ 2`).

* `heredity_step` : one point, gate count `#{i | b ∈ S i, 2 ≤ |S i|}`.
* `base_erase`, `base_erase_deg` : `base(F) = base(F - b) + #{…}` (`= base(F - b) + deg b`).
* `heredity` : one point, all `|S i| ≥ 2`: size `t + deg b`.
* `heredity_multi` : any point set `Z`: `s + base(F - Z) = t + base(F)`.
* `bound_sdiff` : bound(F) ⇒ bound(F - Z).
* `MinCE.min_circuit`, `MinCE.heredity`, `MinCE.heredity_multi` : in a minimal counterexample,
  `s ≤ t + deg b` resp. `s + base(F - Z) ≤ t + base(F)` for every one-NOT circuit of `F - b` resp.
  `F - Z` of size `t`.

Sets that become empty carry no requirement (their outputs may be anything).  No sorry.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section heredity
variable {n m : ℕ}

/-- A wire computing the OR of a nonempty set is an existing wire. -/
theorem lt_of_ev (gates : List Gate) (T : Finset (Fin n)) (o : ℕ) (hT : T.Nonempty)
    (h : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ T, x v = true)) :
    o < n + gates.length := by
  by_contra hge
  have := h (fun _ => true)
  rw [val_ge _ _ _ (by omega)] at this
  obtain ⟨v, hv⟩ := hT
  simp at this
  exact this v hv

theorem hU_snoc (gates : List Gate) (hU : AtMostOneNot gates) (g : Gate)
    (hgn : g.op ≠ GateOp.not) : AtMostOneNot (gates ++ [g]) := by
  intro i1 i2 h1 h2 e1 e2
  have key : ∀ (i : ℕ) (h : i < (gates ++ [g]).length),
      ((gates ++ [g])[i]'h).op = GateOp.not →
      ∃ h' : i < gates.length, (gates[i]'h').op = GateOp.not := by
    intro i h e
    by_cases hi : i < gates.length
    · rw [List.getElem_append_left hi] at e
      exact ⟨hi, e⟩
    · rw [List.getElem_append_right (by omega)] at e
      simp at e
      exact absurd e hgn
  obtain ⟨h1', e1'⟩ := key i1 h1 e1
  obtain ⟨h2', e2'⟩ := key i2 h2 e2
  exact hU i1 i2 h1' h2' e1' e2'

theorem or_erase (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) (x : Fin n → Bool) :
    (decide (∃ v ∈ T.erase b, x v = true) || x b) = decide (∃ v ∈ T, x v = true) := by
  classical
  by_cases h : ∃ v ∈ T, x v = true
  · rw [decide_eq_true h]
    obtain ⟨v, hv, hx⟩ := h
    by_cases hvb : v = b
    · subst hvb; rw [hx]; simp
    · have h1 : ∃ v ∈ T.erase b, x v = true := ⟨v, Finset.mem_erase.mpr ⟨hvb, hv⟩, hx⟩
      rw [decide_eq_true h1]; rfl
  · rw [decide_eq_false h]
    have h1 : ¬ ∃ v ∈ T.erase b, x v = true := fun ⟨v, hv, hx⟩ =>
      h ⟨v, Finset.mem_of_mem_erase hv, hx⟩
    have h2 : x b = false := by
      cases hxb : x b
      · rfl
      · exact absurd ⟨b, hb, hxb⟩ h
    rw [decide_eq_false h1, h2]; rfl

/-- Heredity, one point: from a circuit for `F - b` a circuit for `F` with one more OR gate per set
`S ∋ b`, `|S| ≥ 2`. -/
theorem heredity_step (S : Fin m → Finset (Fin n)) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, ((S i).erase b).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length +
        (Finset.univ.filter fun i : Fin m => b ∈ S i ∧ 2 ≤ (S i).card).card ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  classical
  set B := Finset.univ.filter fun i : Fin m => b ∈ S i with hB
  have main : ∀ A : Finset (Fin m), A ⊆ B → ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length + (A.filter fun i : Fin m => 2 ≤ (S i).card).card ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      (∀ i ∈ A, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true)) ∧
      (∀ i ∉ A, ((S i).erase b).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ (S i).erase b, x v = true)) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨gates', out', by simp, hg, hU, by simp, fun i _ => hev i⟩
    | insert a A ha ih =>
      intro hsub
      obtain ⟨gates, out, hlen, hg1, hU1, hin, hnin⟩ :=
        ih ((Finset.subset_insert a A).trans hsub)
      have hba : b ∈ S a := by
        have := hsub (Finset.mem_insert_self a A)
        simpa [hB] using this
      by_cases hc : 2 ≤ (S a).card
      · have hne : ((S a).erase b).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hba]; omega
        have hoa := hnin a ha hne
        have hlt := lt_of_ev gates _ (out a) hne hoa
        refine ⟨gates ++ [⟨GateOp.or, [out a, (b : ℕ)]⟩],
          Function.update out a (n + gates.length), ?_, ?_, ?_, ?_, ?_⟩
        · rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem
            (fun h => ha (Finset.mem_of_mem_filter a h))]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro g hgm
          rcases List.mem_append.mp hgm with h | h
          · exact hg1 g h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨Or.inr (Or.inl rfl), by simp⟩
        · exact hU_snoc gates hU1 _ (by simp)
        · intro i hi hSi x
          by_cases hia : i = a
          · subst hia
            rw [Function.update_self, val_snoc, if_pos rfl]
            simp only [List.map_cons, List.map_nil]
            rw [hoa x, val_inp _ _ _ b.2, ← or_erase (S i) b hba x]
            simp [GateOp.eval]
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hia
            have hl := lt_of_ev gates _ (out i) hSi (hin i hiA hSi)
            rw [Function.update_of_ne hia, val_snoc, if_neg (by omega)]
            exact hin i hiA hSi x
        · intro i hi hSi x
          have hia : i ≠ a := fun e => hi (e ▸ Finset.mem_insert_self a A)
          have hiA : i ∉ A := fun h => hi (Finset.mem_insert_of_mem h)
          have hl := lt_of_ev gates _ (out i) hSi (hnin i hiA hSi)
          rw [Function.update_of_ne hia, val_snoc, if_neg (by omega)]
          exact hnin i hiA hSi x
      · refine ⟨gates, Function.update out a (b : ℕ), ?_, hg1, hU1, ?_, ?_⟩
        · rw [Finset.filter_insert, if_neg hc]; exact hlen
        · intro i hi hSi x
          by_cases hia : i = a
          · subst hia
            have hSb : S i = {b} := by
              symm
              apply Finset.eq_of_subset_of_card_le (by simpa using hba)
              simp only [Finset.card_singleton]; omega
            rw [Function.update_self, val_inp _ _ _ b.2, hSb]
            simp
          · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hia
            rw [Function.update_of_ne hia]
            exact hin i hiA hSi x
        · intro i hi hSi x
          have hia : i ≠ a := fun e => hi (e ▸ Finset.mem_insert_self a A)
          have hiA : i ∉ A := fun h => hi (Finset.mem_insert_of_mem h)
          rw [Function.update_of_ne hia]
          exact hnin i hiA hSi x
  obtain ⟨gates, out, hlen, hg1, hU1, hin, hnin⟩ := main B (Finset.Subset.refl _)
  refine ⟨gates, out, ?_, hg1, hU1, fun i hSi x => ?_⟩
  · rw [hlen, hB, Finset.filter_filter]
  · by_cases hi : i ∈ B
    · exact hin i hi hSi x
    · have hb : b ∉ S i := by simpa [hB] using hi
      have := hnin i hi (by rw [Finset.erase_eq_of_notMem hb]; exact hSi) x
      rw [Finset.erase_eq_of_notMem hb] at this
      exact this

/-- `base(F) = base(F - b) + #{i | b ∈ S i, 2 ≤ |S i|}`. -/
theorem base_erase (S : Fin m → Finset (Fin n)) (b : Fin n) :
    baseOf S = baseOf (fun i => (S i).erase b) +
      (Finset.univ.filter fun i : Fin m => b ∈ S i ∧ 2 ≤ (S i).card).card := by
  classical
  unfold baseOf
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  beta_reduce
  by_cases hb : b ∈ S i
  · rw [Finset.card_erase_of_mem hb]
    by_cases hc : 2 ≤ (S i).card
    · rw [if_pos ⟨hb, hc⟩]; omega
    · rw [if_neg (fun h => hc h.2)]; omega
  · rw [Finset.erase_eq_of_notMem hb, if_neg (fun h => hb h.1)]; rfl

/-- `base(F) = base(F - b) + deg b` when every set has at least two points. -/
theorem base_erase_deg (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (b : Fin n) : baseOf S = baseOf (fun i => (S i).erase b) + degOf S b := by
  rw [base_erase S b]
  unfold degOf
  congr 2
  ext i
  simp [h2 i]

/-- Heredity (§0): from a one-NOT circuit of size `t` for `F - b` a one-NOT circuit of size
`t + deg b` for `F`. -/
theorem heredity (S : Fin m → Finset (Fin n)) (h2 : ∀ i : Fin m, 2 ≤ (S i).card) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length = gates'.length + degOf S b ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ (i : Fin m) (x : Fin n → Bool), val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  obtain ⟨gates, out, hlen, hg1, hU1, hev1⟩ :=
    heredity_step S b gates' out' hg hU (fun i _ => hev i)
  refine ⟨gates, out, ?_, hg1, hU1, fun i => hev1 i (Finset.card_pos.mp (by have := h2 i; omega))⟩
  have h1 := base_erase S b
  have h2' := base_erase_deg S h2 b
  omega

/-- Heredity for a point set `Z`: from a one-NOT circuit of size `t` for `F - Z` a one-NOT circuit
for `F` of size `s` with `s + base(F - Z) = t + base(F)`. -/
theorem heredity_multi (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n)) :
    ∀ (gates' : List Gate) (out' : Fin m → ℕ),
    (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    AtMostOneNot gates' →
    (∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) →
    ∃ (gates : List Gate) (out : Fin m → ℕ),
      gates.length + baseOf (fun i => S i \ Z) = gates'.length + baseOf S ∧
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      AtMostOneNot gates ∧
      ∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    intro gates' out' hg hU hev
    exact ⟨gates', out', by simp, hg, hU, fun i hi x => by simpa using hev i (by simpa using hi) x⟩
  | insert b Z hb ih =>
    intro gates' out' hg hU hev
    have hfam : ∀ i, S i \ insert b Z = (S i \ Z).erase b := fun i => Finset.sdiff_insert _ _ _
    obtain ⟨g1, o1, hlen1, hg1, hU1, hev1⟩ :=
      heredity_step (fun i => S i \ Z) b gates' out' hg hU (fun i hi x => by
        have := hev i (by rw [hfam]; exact hi) x
        rw [this]; simp only [hfam])
    obtain ⟨g2, o2, hlen2, hg2, hU2, hev2⟩ := ih g1 o1 hg1 hU1 hev1
    refine ⟨g2, o2, ?_, hg2, hU2, hev2⟩
    have hbase := base_erase (fun i => S i \ Z) b
    have : baseOf (fun i => S i \ insert b Z) = baseOf (fun i => (S i \ Z).erase b) := by
      unfold baseOf; simp only [hfam]
    omega

/-- bound(F) ⇒ bound(F - Z): if every one-NOT circuit for `F` has at least `base(F)` gates, then
every one-NOT circuit for `F - Z` has at least `base(F - Z)` gates. -/
theorem bound_sdiff (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n))
    (hF : ∀ (gates : List Gate) (out : Fin m → ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ i : Fin m, (S i).Nonempty → ∀ x : Fin n → Bool,
        val gates x (out i) = decide (∃ v ∈ S i, x v = true)) → baseOf S ≤ gates.length)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) :
    baseOf (fun i => S i \ Z) ≤ gates'.length := by
  obtain ⟨gates, out, hlen, hg1, hU1, hev1⟩ := heredity_multi S Z gates' out' hg hU hev
  have := hF gates out hg1 hU1 hev1
  omega

end heredity

namespace MinCE

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate} {out : Fin m → ℕ}

/-- The circuit of a minimal counterexample is a minimum one-NOT circuit for its sets. -/
theorem min_circuit (M : MinCE S gates out) (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ S i, x v = true)) :
    gates.length ≤ gates'.length := by
  by_contra hlt
  push Not at hlt
  have C := M.ce
  exact M.min n m S gates' out' ⟨C.h2, C.hS, hg, hU, hev, lt_trans hlt C.hlt⟩ (Or.inl hlt)

/-- Heredity in a minimal counterexample: `s(F) + base(F - Z) ≤ s(F - Z) + base(F)` for every
one-NOT circuit of `F - Z` (so `F - Z` is short of its base by at most `σ`). -/
theorem heredity_multi (M : MinCE S gates out) (Z : Finset (Fin n))
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ i : Fin m, (S i \ Z).Nonempty → ∀ x : Fin n → Bool,
      val gates' x (out' i) = decide (∃ v ∈ S i \ Z, x v = true)) :
    gates.length + baseOf (fun i => S i \ Z) ≤ gates'.length + baseOf S := by
  have C := M.ce
  obtain ⟨g1, o1, hlen, hg1, hU1, hev1⟩ :=
    PEqualNP.Outside.L_meta_951_aux.heredity_multi S Z gates' out' hg hU hev
  have := M.min_circuit g1 o1 hg1 hU1
    (fun i => hev1 i (Finset.card_pos.mp (by have := C.h2 i; omega)))
  omega

/-- Heredity in a minimal counterexample, one point: `s(F) ≤ s(F - b) + deg b`. -/
theorem heredity (M : MinCE S gates out) (b : Fin n)
    (gates' : List Gate) (out' : Fin m → ℕ)
    (hg : ∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates')
    (hev : ∀ (i : Fin m) (x : Fin n → Bool),
      val gates' x (out' i) = decide (∃ v ∈ (S i).erase b, x v = true)) :
    gates.length ≤ gates'.length + degOf S b := by
  have C := M.ce
  obtain ⟨g1, o1, hlen, hg1, hU1, hev1⟩ :=
    PEqualNP.Outside.L_meta_951_aux.heredity S C.h2 b gates' out' hg hU hev
  have := M.min_circuit g1 o1 hg1 hU1 hev1
  omega

end MinCE

end PEqualNP.Outside.L_meta_951_aux
