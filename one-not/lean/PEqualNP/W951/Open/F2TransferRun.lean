import PEqualNP.W951.Open.F2Transfer

/-!
# F2TransferRun: unit-form merges are OR gates in F2Mix (seat A6)

Board `open-one-not`. For a one-NOT gate list, a set `w` alive at `Q` and not DD at `(Q, D)`, the merge
set of the `merge_runT` run on the unit-form test system `(Zof (S w ∪ D), Q + e_u, S w \ D)` has at
least `|S w \ D| - 1` wires and lies in `MixedSlack.F2Mix gates S Q D`.
-/

namespace PEqualNP.Outside.L_meta_951_aux.F2Transfer

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

section Run

variable {n m : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

/-- The unit-form merge set of `w` at `(Q, D)`. -/
noncomputable def unitMerge (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m) :
    Finset ℕ :=
  runMT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates gates.length

omit hp hU hN in
include hg in
/-- Merges of a good test system are OR gates. -/
theorem runMT_or (z : Fin n → Bool) (P : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (hT : ∀ u ∈ R, ∀ c : Fin n, P u c = true → z c = false → c = u)
    (hgood : GoodT z P R gates) (j : ℕ) (hj : n + j ∈ runMT z P R gates gates.length) :
    ∃ hjl : j < gates.length, (gates[j]'hjl).op = GateOp.or := by
  classical
  obtain ⟨⟨u, hu, v, hv, hui, hvi, hne⟩, -⟩ :=
    run_recordT z P R gates gates.length j hj
  have hjl : j < gates.length := by
    by_contra h
    rw [mr_val_ge gates _ _ (by omega)] at hui
    exact absurd hui (by simp)
  refine ⟨hjl, ?_⟩
  have hz : val gates z (n + j) = false := by
    have h := run_sub_DT z P R gates _ hj
    simp only [DT, Finset.mem_filter] at h
    exact h.2.1
  have hinv := runLT_inv z P R gates hT j
  rcases (hg _ (List.getElem_mem hjl)).1 with hop | hop | hop
  · exfalso
    rw [mr_val_gate gates z j hjl, hop] at hz
    rw [mr_val_gate gates _ j hjl, hop] at hui hvi
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
      Function.comp_apply, id] at hz hui hvi
    obtain ⟨a, ha, haz⟩ := hz
    have hua := hui a ha
    have hva := hvi a ha
    have ha' : a < n + j := by
      by_contra h
      rw [mr_val_ge (gates.take j) _ a (by simp; omega)] at hua
      exact absurd hua (by simp)
    rw [← mr_val_take gates _ j a ha'] at hua hva
    have haz' : val gates z a = false := by
      rw [mr_val_take gates _ j a ha']
      simpa using haz
    exact hne (hinv a ha' haz' u hu v hv hua hva)
  · exact hop
  · exfalso
    rcases hgood _ _ _ (mr_split gates j hjl) with ⟨h1, -⟩ | h2 | h3
    · rcases h1 with h | h <;> rw [hop] at h <;> exact GateOp.noConfusion h
    · rw [mr_val_gate gates z j hjl] at hz
      rw [hz] at h2
      exact absurd h2 (by simp)
    · rw [mr_val_gate gates _ j hjl] at hui hvi
      exact hne (by rw [h3 u hu v hv hui hvi])

include hg hU hN in
/-- **Unit-form merges of a non-DD set.** With an output wire `out` computing `OR(S w)`: the merge set
has at least `|S w \ D| - 1` wires and lies in `F2Mix`. -/
theorem unitMerge_card_ge_and_subset (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) (w : Fin m)
    (hw : Disjoint Q (S w ∪ D)) (hnd : ¬ DDAt gates p S Q D w) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x out = decide (∃ u ∈ S w, x u = true)) :
    (S w \ D).card - 1 ≤ (unitMerge gates S Q D w).card ∧
      unitMerge gates S Q D w ⊆ MixedSlack.F2Mix gates S Q D := by
  classical
  have hwa : w ∈ aliveSets S Q :=
    mem_aliveSets.mpr (Finset.disjoint_of_subset_left Finset.subset_union_left hw.symm)
  have hT := unit_testSystem (R := S w) (D := D) hw
  have hnd' : hval gates p (Zof (S w ∪ D)) = false ∨
      ∀ u ∈ S w \ D, hval gates p (upPt (canonPt Q) u) = true := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, u, hu, h2⟩ := hcon
    exact hnd ⟨by simpa using h1, u, hu, by simpa using h2⟩
  have hgood := goodT_of_noDD gates p hp hg hU hN (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u)
    (S w \ D) hnd'
  have hzero : ∀ x ∈ S w, Zof (S w ∪ D) x = false := by
    intro x hx
    simp [Zof, hx]
  refine ⟨?_, ?_⟩
  · refine merge_countT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates hT hgood out
      ?_ fun u hu => ?_
    · rw [hev]
      simpa using fun y hy => hzero y hy
    · rw [hev]
      exact decide_eq_true ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [upPt]⟩
  · intro i hi
    obtain ⟨j, -, rfl, -⟩ :=
      (runMT_mem (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates gates.length i).mp hi
    obtain ⟨hjl, hor⟩ := runMT_or gates hg (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D)
      hT hgood j hi
    obtain ⟨⟨u, hu, u', hu', h1, h2, hne⟩, -⟩ :=
      run_recordT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates gates.length j hi
    have huu : u ≠ u' := fun h => hne (h ▸ rfl)
    have h0 : val gates (Zof (S w ∪ D)) (n + j) = false := by
      have h := run_sub_DT (Zof (S w ∪ D)) (fun u => upPt (canonPt Q) u) (S w \ D) gates _ hi
      simp only [DT, Finset.mem_filter] at h
      exact h.2.1
    have hij : n + j ∈ Finset.Ico n (n + gates.length) := by
      rw [Finset.mem_Ico]; omega
    simp only [MixedSlack.F2Mix, Finset.mem_filter]
    refine ⟨hij, ?_, w, hwa, ?_⟩
    · show IsOrAt gates (n + j - n)
      rw [Nat.add_sub_cancel_left]
      exact ⟨gates[j], List.getElem?_eq_getElem hjl, hor⟩
    exact F2WitMix_of_unit_noDD gates p hp hg hU hN S w Q D hw hnd _ h0 hu hu' huu h1 h2

end Run

end PEqualNP.Outside.L_meta_951_aux.F2Transfer
