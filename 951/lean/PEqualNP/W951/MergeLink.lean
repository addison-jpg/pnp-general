import PEqualNP.W951.MergeFrac
import PEqualNP.W951.LiftHelpers

/-! MergeLink: the load condition `hload` of `liftClassFrac_of_realBasePoints` (LiftHelpers) gives
MergeFrac, with the same weights.

The two `no_minCE` targets on the fractional route charge different sets at the same points:
* `hload` (LiftHelpers): weights `lam w j` on zero points `z w j` of `S w`, and every gate `i ≠ p`
  has load `≤ 1` over the WHOLE classes `RealCl gates p (S w) (z w j) i` (OR gate, `0` at `z`,
  `1` at two or more `z + e_u`, `u ∈ S w`, read in the world of `z`); it gives `LiftClassFrac`,
  hence `s ≥ base + 1`.
* `MergeFrac` (MergeFrac.lean): distributions on zero points, and every wire has load `≤ 1` over
  the MERGE SETS `M_z(w)` (exactly `|S w| - 1` gates, Lemma M); it gives `FracMatch`, hence
  `s ≥ base`. `MergePrice` is its LP dual (`mergeFrac_iff_mergePrice`).

`realCl_of_mem_mergeSet`: every merge gate of `S` at a zero point `z` is in the class `RealCl` of
`z` (merges are OR gates, `mergeSet_or`; the NOT gate is not an OR gate; the real circuit lies
between the worlds `C0 ≤ real ≤ C1`, and on `{h = 1}` it equals `C0`). Hence
`mergeFrac_of_realBasePoints`: a weighting that satisfies `hload` satisfies MergeFrac. So
`MergeFrac` / `MergePrice` is the weaker target, and every result on either route lands in
`no_minCE_of_mergePrice`. The converse fails as a method: whole-class charging is refuted on cxT2
and cxT4 (front-match w9/chist_fable.md C1), while MergeFrac holds on every circuit checked
(about 15,300, C6). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

open Classical in
/-- **Merge sets lie in the real-base-point classes.** For the NOT gate at `p` and a point `z`
vanishing on `R`, every merge gate `n + i` of `R` at `z` is in `RealCl gates p R z i`. -/
theorem realCl_of_mem_mergeSet {n : ℕ} (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (R : Finset (Fin n))
    (z : Fin n → Bool) (i : ℕ) (hi : n + i ∈ mergeSet gates R z) : RealCl gates p R z i := by
  obtain ⟨hil, hor⟩ := mergeSet_or gates hg hU R z i hi
  have hD := mergeSet_subset_DT gates R z hi
  simp only [DT, Finset.mem_filter] at hD
  obtain ⟨-, hz, u, v, huv, hu, hv, hgu, hgv⟩ := hD
  have hip : i ≠ p := by
    rintro rfl
    rw [hN] at hor
    exact GateOp.noConfusion hor
  -- a real `1` at a test point is a `1` in the world of `z`
  have hworld : ∀ x, z ≤ x → val gates x (n + i) = true →
      val (wld (!hval gates p z) gates) x (n + i) = true := by
    intro x hzx hx
    cases hh : hval gates p z
    · simp only [Bool.not_false, wld, ite_true]
      exact ((sandwich gates (fun g hg' => (hg g hg').1) x) (n + i)).2 hx
    · simp only [Bool.not_true]
      rw [val_wld_false_of_hval gates p hp hU hN x
        (hval_mono gates p hp hg hU hN hzx hh) (n + i)]
      exact hx
  refine ⟨hil, hip, ⟨gates[i]'hil, List.getElem?_eq_getElem hil, hor⟩, hz,
    Finset.one_lt_card.mpr ⟨u, ?_, v, ?_, huv⟩⟩
  · exact Finset.mem_filter.mpr ⟨hu, hworld _ (le_upPt z u) hgu⟩
  · exact Finset.mem_filter.mpr ⟨hv, hworld _ (le_upPt z v) hgv⟩

open Classical in
/-- **`hload` gives MergeFrac.** The load hypothesis of `liftClassFrac_of_realBasePoints` (weights
`lam w j` on zero points `z w j`, whole classes `RealCl`, load `≤ 1` at every gate `i ≠ p`)
implies `MergeFrac`, with `μ w` the same mixture of the points `z w j`. -/
theorem mergeFrac_of_realBasePoints {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if RealCl gates p (S w) (z w j) i then lam w j else 0) ≤ 1) :
    MergeFrac S gates := by
  refine ⟨fun w x => ∑ j, if z w j = x then lam w j else 0, ?_, ?_, ?_, ?_⟩
  · intro w x
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hlam0]
  · rintro w x ⟨v, hv, hxv⟩
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    rintro rfl
    rw [hz w j v hv] at hxv
    exact absurd hxv (by simp)
  · intro w
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hlam1 w
  · intro g
    -- the load of `g` is the load over the points `z w j`
    have hre : ∀ w, ∑ x, (if g ∈ mergeSet gates (S w) x then
        ∑ j, (if z w j = x then lam w j else 0) else 0) =
        ∑ j, (if g ∈ mergeSet gates (S w) (z w j) then lam w j else 0) := by
      intro w
      trans ∑ x, ∑ j, (if z w j = x then
          (if g ∈ mergeSet gates (S w) x then lam w j else 0) else 0)
      · refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hg : g ∈ mergeSet gates (S w) x
        · simp only [hg, ite_true]
        · simp only [hg, ite_false, ite_self, Finset.sum_const_zero]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    simp only [hre]
    by_cases hex : ∃ i, i < gates.length ∧ i ≠ p ∧ g = n + i
    · obtain ⟨i, hi, hip, rfl⟩ := hex
      refine le_trans (Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun j _ => ?_)
        (hload i hi hip)
      by_cases hm : n + i ∈ mergeSet gates (S w) (z w j)
      · rw [ite_eq_left hm, ite_eq_left (realCl_of_mem_mergeSet gates p hp hg hU hN (S w) (z w j) i hm)]
      · rw [ite_eq_right hm]
        split_ifs
        · exact hlam0 w j
        · exact le_rfl
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun j _ => ?_)
        zero_le_one
      rw [ite_eq_right]
      intro hm
      have hI := Finset.mem_Ico.mp (mergeSet_subset gates (S w) (z w j) hm)
      obtain ⟨i, rfl⟩ : ∃ i, g = n + i := ⟨g - n, by omega⟩
      have hR := realCl_of_mem_mergeSet gates p hp hg hU hN (S w) (z w j) i hm
      exact hex ⟨i, hR.1, hR.2.1, rfl⟩

open Classical in
/-- **`hload` gives MergePrice** (the price form front attacks), by LP duality. -/
theorem mergePrice_of_realBasePoints {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (p : ℕ) (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
    (k : Fin m → ℕ) (z : ∀ w, Fin (k w) → Fin n → Bool) (lam : ∀ w, Fin (k w) → ℝ)
    (hlam0 : ∀ w j, 0 ≤ lam w j) (hlam1 : ∀ w, ∑ j, lam w j = 1)
    (hz : ∀ w j, ∀ v ∈ S w, z w j v = false)
    (hload : ∀ i : ℕ, i < gates.length → i ≠ p → ∑ w, ∑ j,
      (if RealCl gates p (S w) (z w j) i then lam w j else 0) ≤ 1) :
    MergePrice S gates :=
  mergePrice_of_mergeFrac S gates
    (mergeFrac_of_realBasePoints S gates p hp hg hU hN k z lam hlam0 hlam1 hz hload)

end PEqualNP.Outside.L_meta_951_aux
