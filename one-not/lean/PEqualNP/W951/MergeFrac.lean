import PEqualNP.Base.Matching.Duality
import PEqualNP.W951.MergeRunTSys
import PEqualNP.W951.PriceForm
import PEqualNP.W951.LiftFrac

/-! MergeFrac: the canonical merge sets at every zero point, and the fractional target built
on them (front, SORRY_DISSECTION §20 / w9/chist_fable.md C6).

For a set `R` and ANY point `z` vanishing on `R`, the test points are `z + e_u` (`upPt z u`), and
`mergeSet gates R z` is the merge set of the union-find run of `MergeRunT.lean` over the whole
circuit (no masking, no `Good` hypothesis beyond "AND/OR/NOT of fan-in ≤ 2, at most one NOT").

* Level 1 (Lemma M): `mergeSet_card` — `|M_z(w)| = |S_w| - 1` EXACTLY (`mergeSet_card_le` needs
  no hypothesis at all; `mergeSet_card_ge` is `merge_countT`). `mergeSet_or`: merges are OR gates.
* Level 2: `MergeFrac`, `fracMatch_of_mergeFrac`, `bound_of_mergeFrac`, `no_minCE_of_mergeFrac`,
  and the load identity `mergeFrac_load_sum`.
* Level 3: `MergePrice` (dual form), `mergeFrac_iff_mergePrice` (LP duality), and the proved
  single-price case `univMerge_disjoint` / `mergePrice_single`.
* Level 4 (chist C0, C2, C3): `subselection_bound` (form (U), primal arithmetic); `CoverPrice`
  (dual of (U)), `bound_of_coverPrice`, `coverPrice_of_priceIneq`, `coverPrice_of_mergeFrac`;
  `Servable`, Lemma R `servable_of_gate`, Theorem F `servablePacking_mono` (monotone core) and
  `bound_of_servablePacking` (`s ≥ 1 + V_fun`), `IsCE.servablePacking_le` (`V_fun ≤ base - 2` on
  every counterexample). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-! ## Level 1: Lemma M -/

/-- The test point `z + e_u`. -/
def upPt {n : ℕ} (z : Fin n → Bool) (u : Fin n) : Fin n → Bool := Function.update z u true

theorem le_upPt {n : ℕ} (z : Fin n → Bool) (u : Fin n) : z ≤ upPt z u := by
  intro c
  by_cases h : c = u
  · subst h; simp [upPt]
  · simp [upPt, Function.update_of_ne h]

theorem upPt_hT {n : ℕ} (z : Fin n → Bool) (u c : Fin n) (h : upPt z u c = true)
    (hc : z c = false) : c = u := by
  by_contra hne
  rw [upPt, Function.update_of_ne hne, hc] at h
  exact absurd h (by simp)

/-- **The merge set `M_z`** of a set `R` at the point `z`: the wires at which the union-find run
over the wires that are `0` at `z` (test points `z + e_u`, `u ∈ R`) merges two blocks. -/
def mergeSet {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) : Finset ℕ :=
  runMT z (upPt z) R gates gates.length

/-- With at most one NOT, the whole circuit is `GoodT` at every point `z` for the test points
`z + e_u`: a NOT gate that is `0` at `z` reads a wire of the AND/OR prefix that is `1` at `z`,
hence `1` at every `z + e_u`, so the NOT gate is `0` at all test points. -/
theorem goodT_upPt {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (z : Fin n → Bool) (R : Finset (Fin n)) :
    GoodT z (upPt z) R gates := by
  intro pre g rest h
  have hmem : g ∈ gates := by rw [h]; simp
  rcases (hg g hmem).1 with hop | hop | hop
  · exact Or.inl ⟨Or.inl hop, (hg g hmem).2⟩
  · exact Or.inl ⟨Or.inr hop, (hg g hmem).2⟩
  right
  have hpre : ∀ g' ∈ pre, g'.op = GateOp.and ∨ g'.op = GateOp.or := by
    intro g' hg'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg'
    have hiL : i < gates.length := by rw [h]; simp; omega
    have hpL : pre.length < gates.length := by rw [h]; simp
    have e1 : gates[i]'hiL = pre[i] := by simp [h, List.getElem_append_left hi]
    have e2 : gates[pre.length]'hpL = g := by simp [h]
    rcases (hg _ (List.getElem_mem hiL)).1 with h' | h' | h'
    · exact Or.inl (e1 ▸ h')
    · exact Or.inr (e1 ▸ h')
    · exact absurd (hU i pre.length hiL hpL h' (e2 ▸ hop)) (by omega)
  rw [hop]
  cases hin : g.inputs with
  | nil => exact Or.inl (by simp [GateOp.eval])
  | cons j r =>
    cases hz : val pre z j
    · exact Or.inl (by simp [GateOp.eval, hz])
    · refine Or.inr fun u _ v _ hu _ => ?_
      have h1 := Bool.le_iff_imp.mp (val_le_of_le pre hpre (le_upPt z u) j) hz
      simp [GateOp.eval, h1] at hu

section Count

variable {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
  (gs : List Gate)

/-- A merge lowers the number of blocks by at least one (no hypothesis). -/
theorem img_merge_ltT (l : Fin n → Fin n) (k : ℕ) (hm : MgT z p R gs l k) :
    (R.image (mstepT z p R gs l k)).card + 1 ≤ (R.image l).card := by
  classical
  set T := (trRT p R gs (n + k)).image l with hT
  have hr : mrep _ hm.2 ∈ T := Finset.min'_mem _ _
  have hTR : T ⊆ R.image l := Finset.image_subset_image (Finset.filter_subset _ _)
  have hsub : R.image (mstepT z p R gs l k) ⊆ R.image l \ T.erase (mrep _ hm.2) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    rw [mstepT_apply z p R gs hm, Finset.mem_sdiff]
    split_ifs with hyS
    · exact ⟨hTR hr, fun h => (Finset.mem_erase.mp h).1 rfl⟩
    · exact ⟨Finset.mem_image_of_mem l hw, fun h => hyS (Finset.mem_erase.mp h).2⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (R.image l \ T.erase (mrep _ hm.2)).card + (T.erase (mrep _ hm.2)).card
      = (R.image l).card :=
    Finset.card_sdiff_add_card_eq_card ((Finset.erase_subset _ _).trans hTR)
  have h3 := Finset.card_erase_of_mem hr
  have h4 : 1 < T.card := hm.2
  omega

/-- Upper count of the run: blocks plus merges never exceed `|R|` (no hypothesis). -/
theorem run_count_leT (k : ℕ) :
    (R.image (runLT z p R gs k)).card + (runMT z p R gs k).card ≤ R.card := by
  induction k with
  | zero => simp [runLT, runMT]
  | succ k ih =>
    by_cases hm : MgT z p R gs (runLT z p R gs k) k
    · have hM : runMT z p R gs (k + 1) = insert (n + k) (runMT z p R gs k) := by
        rw [runMT, ite_eq_left hm]
      have hnot : n + k ∉ runMT z p R gs k := by
        rw [runMT_mem]
        rintro ⟨j, hj, he, -⟩
        omega
      rw [runLT_succ, hM, Finset.card_insert_of_notMem hnot]
      have := img_merge_ltT z p R gs _ k hm
      omega
    · have hM : runMT z p R gs (k + 1) = runMT z p R gs k := by
        rw [runMT, ite_eq_right hm]
      rw [runLT_succ, hM, mstepT_nomerge z p R gs hm]
      exact ih

/-- The merge set of any run has at most `|R| - 1` elements (no hypothesis). -/
theorem runMT_card_le (k : ℕ) : (runMT z p R gs k).card ≤ R.card - 1 := by
  have h := run_count_leT z p R gs k
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR; simp at h ⊢; exact h
  · have : 0 < (R.image (runLT z p R gs k)).card := Finset.card_pos.mpr (hR.image _)
    omega

end Count

/-- Lemma M, upper half: `|M_z| ≤ |R| - 1`, for every circuit, set and point. -/
theorem mergeSet_card_le {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    (mergeSet gates R z).card ≤ R.card - 1 :=
  runMT_card_le z (upPt z) R gates gates.length

/-- Merge wires are gate wires. -/
theorem mergeSet_subset {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    mergeSet gates R z ⊆ Finset.Ico n (n + gates.length) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := run_indexT z (upPt z) R gates _ i hi
  simp [hj]

/-- Merge wires are counted wires (`DT`) of the unmasked circuit. -/
theorem mergeSet_subset_DT {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    mergeSet gates R z ⊆ DT z (upPt z) R gates :=
  run_sub_DT z (upPt z) R gates _

/-- Lemma M, lower half (`merge_countT`): if wire `o` is `0` at `z` and `1` at every `z + e_u`,
`u ∈ R`, then `|M_z| ≥ |R| - 1`. -/
theorem mergeSet_card_ge {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (R : Finset (Fin n)) (z : Fin n → Bool) (o : ℕ)
    (hzo : val gates z o = false) (hpo : ∀ u ∈ R, val gates (upPt z u) o = true) :
    R.card - 1 ≤ (mergeSet gates R z).card :=
  merge_countT z (upPt z) R gates (fun u _ c => upPt_hT z u c) (goodT_upPt gates hg hU z R) o
    hzo hpo

/-- **Lemma M** (exact form). For ANY point `z` (no `Good` condition): if wire `o` is `0` at `z`
and `1` at every `z + e_u`, `u ∈ R`, the union-find run over the wires `0` at `z` has exactly
`|R| - 1` merging gates. -/
theorem mergeSet_card' {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (R : Finset (Fin n)) (z : Fin n → Bool) (o : ℕ)
    (hzo : val gates z o = false) (hpo : ∀ u ∈ R, val gates (upPt z u) o = true) :
    (mergeSet gates R z).card = R.card - 1 :=
  le_antisymm (mergeSet_card_le gates R z) (mergeSet_card_ge gates hg hU R z o hzo hpo)

/-- **Lemma M** for a circuit computing `OR(S)` at `o`: at every point `z` vanishing on `S`,
`|M_z| = |S| - 1` exactly. -/
theorem mergeSet_card {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (S : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ S, x v = true))
    (z : Fin n → Bool) (hz : ∀ v ∈ S, z v = false) :
    (mergeSet gates S z).card = S.card - 1 := by
  apply mergeSet_card' gates hg hU S z o
  · rw [hev, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv'⟩
    rw [hz v hv] at hv'
    exact absurd hv' (by simp)
  · intro u hu
    rw [hev, decide_eq_true_eq]
    exact ⟨u, hu, by simp [upPt]⟩

/-- **Merges are OR gates** (any circuit with AND/OR/NOT of fan-in at most 2 and at most one NOT,
any set, any point). An AND gate that is `0` at `z` has an input that is `0` at `z` and `1` on the
whole trace of the gate, so the run invariant puts the trace in one block; a NOT gate that is `0`
at `z` is `1` at no test point (`goodT_upPt`). -/
theorem mergeSet_or {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (R : Finset (Fin n)) (z : Fin n → Bool) (j : ℕ)
    (hj : n + j ∈ mergeSet gates R z) :
    ∃ hjl : j < gates.length, (gates[j]'hjl).op = GateOp.or := by
  classical
  obtain ⟨⟨u, hu, v, hv, hui, hvi, hne⟩, -⟩ :=
    run_recordT z (upPt z) R gates gates.length j hj
  have hjl : j < gates.length := by
    by_contra h
    rw [mr_val_ge gates _ _ (by omega)] at hui
    exact absurd hui (by simp)
  refine ⟨hjl, ?_⟩
  have hz : val gates z (n + j) = false := by
    have h := mergeSet_subset_DT gates R z hj
    simp only [DT, Finset.mem_filter] at h
    exact h.2.1
  have hinv := runLT_inv z (upPt z) R gates (fun u _ c => upPt_hT z u c) j
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
    rcases goodT_upPt gates hg hU z R _ _ _ (mr_split gates j hjl) with ⟨h1, -⟩ | h2 | h3
    · rcases h1 with h | h <;> rw [hop] at h <;> exact GateOp.noConfusion h
    · rw [mr_val_gate gates z j hjl] at hz
      rw [hz] at h2
      exact absurd h2 (by simp)
    · rw [mr_val_gate gates _ j hjl] at hui hvi
      exact hne (by rw [h3 u hu v hv hui hvi])

/-- The test system of a zero point: `z`, test points `z + e_u`, all gates kept. -/
def zeroSys {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (S : Finset (Fin n)) (o : ℕ) (z : Fin n → Bool)
    (hz : ∀ v ∈ S, z v = false) : TestSys n gates S o where
  z := z
  p := upPt z
  K := Finset.range gates.length
  hzS := hz
  hpS := fun u _ => by simp [upPt]
  hT := fun u _ c => upPt_hT z u c
  hcl := fun k _ _ i _ h1 h2 => by rw [Finset.mem_range]; omega
  hout := by
    by_cases h1 : o < n
    · exact Or.inl h1
    · by_cases h2 : n + gates.length ≤ o
      · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl (by rw [Finset.mem_range]; omega))
  hgood := by rw [mask_range gates _ le_rfl]; exact goodT_upPt gates hg hU z S

/-- The merge set lies in the counted wires of `zeroSys`. -/
theorem mergeSet_subset_cnt {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (S : Finset (Fin n)) (o : ℕ) (z : Fin n → Bool)
    (hz : ∀ v ∈ S, z v = false) :
    mergeSet gates S z ⊆ (zeroSys gates hg hU S o z hz).cnt := by
  have h : (zeroSys gates hg hU S o z hz).cnt = DT z (upPt z) S gates := by
    show DT z (upPt z) S (mask (Finset.range gates.length) gates) = _
    rw [mask_range gates _ le_rfl]
  rw [h]
  exact mergeSet_subset_DT gates S z

/-! ## Level 2: MergeFrac ⇒ FracMatch ⇒ the bound -/

/-- **MergeFrac** (OPEN in general): probability distributions `μ w` on the zero points of `S w`
(points vanishing on `S w`) such that every wire `g` has load
`∑ w, ∑ z, μ w z * [g ∈ M_z(w)] ≤ 1`. -/
def MergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∃ μ : Fin m → (Fin n → Bool) → ℝ,
    (∀ w z, 0 ≤ μ w z) ∧ (∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) ∧
    (∀ w, ∑ z, μ w z = 1) ∧
    ∀ g : ℕ, ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0) ≤ 1

/-- **MergeFrac ⇒ FracMatch**: the systems are `zeroSys` at the zero points, the sets are the
merge sets (inside `cnt`, of size `|S w| - 1` by Lemma M). -/
theorem fracMatch_of_mergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hf : MergeFrac S gates) : FracMatch S gates out := by
  classical
  obtain ⟨μ, h0, hsupp, h1, hload⟩ := hf
  let e : Fin (Fintype.card (Fin n → Bool)) ≃ (Fin n → Bool) := (Fintype.equivFin _).symm
  let zf : Fin m → (Fin n → Bool) → (Fin n → Bool) := fun w z =>
    if ∀ v ∈ S w, z v = false then z else fun _ => false
  have hzf : ∀ w z, ∀ v ∈ S w, zf w z v = false := by
    intro w z v hv
    simp only [zf]
    split_ifs with h
    · exact h v hv
    · rfl
  have hzfe : ∀ w z, μ w z ≠ 0 → zf w z = z := by
    intro w z hne
    simp only [zf]
    rw [ite_eq_left]
    intro v hv
    by_contra hc
    exact hne (hsupp w z ⟨v, hv, by simpa using hc⟩)
  refine ⟨fun _ => Fintype.card (Fin n → Bool),
    fun w j => zeroSys gates hg hU (S w) (out w) (zf w (e j)) (hzf w _),
    fun w j => μ w (e j), fun w j => mergeSet gates (S w) (zf w (e j)), fun w j => h0 w _,
    fun w => ?_, fun w j => mergeSet_subset_cnt gates hg hU (S w) (out w) _ (hzf w _),
    fun w j => (mergeSet_card gates hg hU (S w) (out w) (hev w) _ (hzf w _)).ge, fun g => ?_⟩
  · exact (e.sum_comp (μ w)).trans (h1 w)
  · refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) (hload g)
    rw [← e.sum_comp (fun z => if g ∈ mergeSet gates (S w) z then μ w z else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hne : μ w (e j) = 0
    · simp [hne]
    · show (if g ∈ mergeSet gates (S w) (zf w (e j)) then μ w (e j) else 0) = _
      rw [hzfe w _ hne]

/-- MergeFrac gives the bound. -/
theorem bound_of_mergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hf : MergeFrac S gates) : ∑ i : Fin m, ((S i).card - 1) ≤ gates.length :=
  bound_of_fracMatch S gates out (fracMatch_of_mergeFrac S gates out hg hU hev hf)

/-- A circuit with a MergeFrac family is not a counterexample. -/
theorem not_isCE_of_mergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hf : MergeFrac S gates) : ¬ IsCE S gates out := by
  intro C
  have := bound_of_mergeFrac S gates out C.hg C.hU C.hev hf
  have := C.hlt
  omega

/-- **MergeFrac on minimal counterexamples closes 951.** -/
theorem no_minCE_of_mergeFrac
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → MergeFrac S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  fun {n m} S gates out M => not_isCE_of_mergeFrac S gates out (H n m S gates out M) M.ce

/-- **Load identity**: for any distributions on zero points the total load is the base
`∑ w, (|S w| - 1)` (so MergeFrac needs at least `base` loaded gates, each exactly full when
`gates.length = base`). -/
theorem mergeFrac_load_sum {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (μ : Fin m → (Fin n → Bool) → ℝ)
    (hsupp : ∀ w z, (∃ v ∈ S w, z v = true) → μ w z = 0) (h1 : ∀ w, ∑ z, μ w z = 1) :
    ∑ g ∈ Finset.Ico n (n + gates.length),
        ∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0)
      = ∑ w, (((S w).card - 1 : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_comm]
  trans ∑ z, μ w z * (((S w).card - 1 : ℕ) : ℝ)
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (mergeSet_subset gates (S w) z), Finset.sum_const, nsmul_eq_mul]
    by_cases hne : μ w z = 0
    · simp [hne]
    · rw [mergeSet_card gates hg hU (S w) (out w) (hev w) z, mul_comm]
      intro v hv
      by_contra hc
      exact hne (hsupp w z ⟨v, hv, by simpa using hc⟩)
  · rw [← Finset.sum_mul, h1 w, one_mul]

/-! ## Level 3: the dual (price) form -/

/-- The zero points of `R`: the points vanishing on `R`. -/
def zeroPts {n : ℕ} (R : Finset (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun z => ∀ v ∈ R, z v = false

theorem mem_zeroPts {n : ℕ} {R : Finset (Fin n)} {z : Fin n → Bool} :
    z ∈ zeroPts R ↔ ∀ v ∈ R, z v = false := by simp [zeroPts]

theorem zeroPts_nonempty {n : ℕ} (R : Finset (Fin n)) : (zeroPts R).Nonempty :=
  ⟨fun _ => false, by simp [zeroPts]⟩

/-- **MergePrice**, the dual form of MergeFrac: for every nonnegative pricing of the wires,
the cheapest merge sets, summed over the sets, cost at most all gate wires:
`∑ w, min_z π(M_z(w)) ≤ π(gates)`. -/
def MergePrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) : Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    ∑ w, (zeroPts (S w)).inf' (zeroPts_nonempty _)
        (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
      ≤ ∑ g ∈ Finset.Ico n (n + gates.length), π g

/-- Weak duality (direct). -/
theorem mergePrice_of_mergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hf : MergeFrac S gates) : MergePrice S gates := by
  classical
  obtain ⟨μ, h0, hsupp, h1, hload⟩ := hf
  intro π hπ
  calc ∑ w, (zeroPts (S w)).inf' (zeroPts_nonempty _)
          (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
      ≤ ∑ w, ∑ z, μ w z * ∑ g ∈ mergeSet gates (S w) z, π g := by
        refine Finset.sum_le_sum fun w _ => ?_
        calc (zeroPts (S w)).inf' (zeroPts_nonempty _)
              (fun z => ∑ g ∈ mergeSet gates (S w) z, π g)
            = ∑ z, μ w z * (zeroPts (S w)).inf' (zeroPts_nonempty _)
                (fun z => ∑ g ∈ mergeSet gates (S w) z, π g) := by
              rw [← Finset.sum_mul, h1 w, one_mul]
          _ ≤ _ := Finset.sum_le_sum fun z _ => ?_
        by_cases hz : z ∈ zeroPts (S w)
        · exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hz) (h0 w z)
        · have hμ : μ w z = 0 := by
            apply hsupp w z
            by_contra hc
            exact hz (mem_zeroPts.mpr fun v hv => by
              by_contra hv'
              exact hc ⟨v, hv, by simpa using hv'⟩)
          simp [hμ]
    _ = ∑ g ∈ Finset.Ico n (n + gates.length),
          (∑ w, ∑ z, (if g ∈ mergeSet gates (S w) z then μ w z else 0)) * π g := by
        symm
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [ite_mul, zero_mul]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (mergeSet_subset gates (S w) z), Finset.mul_sum]
    _ ≤ ∑ g ∈ Finset.Ico n (n + gates.length), 1 * π g :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hload g) (hπ g)
    _ = _ := by simp

/-- The gate indices of a merge set. -/
def mergeIdx {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    Finset (Fin gates.length) :=
  Finset.univ.filter fun i => n + (i : ℕ) ∈ mergeSet gates R z

theorem mem_mergeIdx {n : ℕ} {gates : List Gate} {R : Finset (Fin n)} {z : Fin n → Bool}
    {i : Fin gates.length} : i ∈ mergeIdx gates R z ↔ n + (i : ℕ) ∈ mergeSet gates R z := by
  simp [mergeIdx]

theorem mergeIdx_map {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool) :
    (mergeIdx gates R z).map (wireEmb n gates.length) = mergeSet gates R z := by
  ext g
  simp only [mergeIdx, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    wireEmb_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hg
    have h := Finset.mem_Ico.1 (mergeSet_subset gates R z hg)
    exact ⟨⟨g - n, by omega⟩, by simpa [Nat.add_sub_cancel' h.1] using hg,
      Nat.add_sub_cancel' h.1⟩

theorem sum_mergeSet {n : ℕ} (gates : List Gate) (R : Finset (Fin n)) (z : Fin n → Bool)
    (π : ℕ → ℝ) :
    ∑ g ∈ mergeSet gates R z, π g = ∑ a ∈ mergeIdx gates R z, π (n + (a : ℕ)) := by
  rw [← mergeIdx_map, Finset.sum_map]
  rfl

/-- Strong duality (`exists_frac_iff_prices`): the price form gives the distributions. -/
theorem mergeFrac_of_mergePrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (hp : MergePrice S gates) : MergeFrac S gates := by
  classical
  set O : Fin m → Finset (Finset (Fin gates.length)) :=
    fun w => (zeroPts (S w)).image (mergeIdx gates (S w)) with hOdef
  have hO : ∀ w, (O w).Nonempty := fun w => (zeroPts_nonempty _).image _
  have hprice : ∀ π' : Fin gates.length → ℝ, (∀ a, 0 ≤ π' a) →
      ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π' a) ≤ ∑ a, π' a := by
    intro π' hπ'
    set π : ℕ → ℝ := fun g => if h : g - n < gates.length then π' ⟨g - n, h⟩ else 0 with hπdef
    have hπ : ∀ g, 0 ≤ π g := by
      intro g
      simp only [hπdef]
      split_ifs
      · exact hπ' _
      · exact le_rfl
    have hπe : ∀ a : Fin gates.length, π (n + a) = π' a := by
      intro a
      simp [hπdef]
    have h := hp π hπ
    rw [sum_Ico_eq_sum_fin] at h
    simp only [hπe] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) h
    simp only [hOdef]
    rw [Finset.inf'_image]
    refine Finset.inf'_congr _ rfl fun z _ => ?_
    simp only [Function.comp_apply, sum_mergeSet, hπe]
  obtain ⟨lam, hlam, hl⟩ := (exists_frac_iff_prices O hO).2 hprice
  have hrep : ∀ w M, M ∈ O w → ∃ z, z ∈ zeroPts (S w) ∧ mergeIdx gates (S w) z = M :=
    fun w M h => by simpa [hOdef] using h
  let rep : Fin m → Finset (Fin gates.length) → (Fin n → Bool) := fun w M =>
    if h : M ∈ O w then (hrep w M h).choose else fun _ => false
  have hrep1 : ∀ w M, M ∈ O w →
      rep w M ∈ zeroPts (S w) ∧ mergeIdx gates (S w) (rep w M) = M := by
    intro w M h
    simp only [rep, dite_eq_left h]
    exact (hrep w M h).choose_spec
  refine ⟨fun w z => ∑ M ∈ O w, if rep w M = z then lam w M else 0, ?_, ?_, ?_, ?_⟩
  · intro w z
    refine Finset.sum_nonneg fun M _ => ?_
    split_ifs
    · exact hlam.1 w M
    · exact le_rfl
  · rintro w z ⟨v, hv, hzv⟩
    refine Finset.sum_eq_zero fun M hM => ?_
    rw [ite_eq_right]
    rintro rfl
    rw [mem_zeroPts.mp (hrep1 w M hM).1 v hv] at hzv
    exact absurd hzv (by simp)
  · intro w
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hlam.2.2 w
  · intro g
    by_cases hgI : g ∈ Finset.Ico n (n + gates.length)
    · have hI := Finset.mem_Ico.1 hgI
      obtain ⟨a, rfl⟩ : ∃ a : Fin gates.length, g = n + (a : ℕ) :=
        ⟨⟨g - n, by omega⟩, by simp; omega⟩
      refine le_of_eq_of_le ?_ (hl a)
      unfold load
      refine Finset.sum_congr rfl fun w _ => ?_
      trans ∑ z, ∑ M ∈ O w, if rep w M = z then
          (if n + (a : ℕ) ∈ mergeSet gates (S w) z then lam w M else 0) else 0
      · refine Finset.sum_congr rfl fun z _ => ?_
        by_cases h : n + (a : ℕ) ∈ mergeSet gates (S w) z <;> simp [h]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun M hM => ?_
      rw [Finset.sum_ite_eq]
      have hiff : a ∈ M ↔ n + (a : ℕ) ∈ mergeSet gates (S w) (rep w M) := by
        rw [← mem_mergeIdx, (hrep1 w M hM).2]
      by_cases h : a ∈ M
      · simp [h, hiff.mp h]
      · have hn : n + (a : ℕ) ∉ mergeSet gates (S w) (rep w M) := fun h' => h (hiff.mpr h')
        simp [h, hn]
    · exact le_of_eq_of_le (Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun z _ =>
        ite_eq_right fun h => hgI (mergeSet_subset _ _ _ h)) zero_le_one

/-- **LP duality: MergeFrac ⇔ MergePrice** (`∀ π ≥ 0, ∑ w, min_z π(M_z(w)) ≤ π(gates)`). -/
theorem mergeFrac_iff_mergePrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) :
    MergeFrac S gates ↔ MergePrice S gates :=
  ⟨mergePrice_of_mergeFrac S gates, mergeFrac_of_mergePrice S gates⟩

/-- **MergePrice on minimal counterexamples closes 951.** -/
theorem no_minCE_of_mergePrice
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → MergePrice S gates) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergeFrac fun n m S gates out M =>
    mergeFrac_of_mergePrice S gates (H n m S gates out M)

/-- **Universal merges are pairwise disjoint** (the single-price case, any circuit): no wire is
a merge of two different sets at ALL their zero points. Such a wire is `1` at two units
`e_u, e_v` of `S a` (zero point `0`), and `0` at every point avoiding `S b`, so `u, v ∈ S b`. -/
theorem univMerge_disjoint {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (gates : List Gate) (a b : Fin m)
    (hab : a ≠ b) (g : ℕ) (ha : ∀ z ∈ zeroPts (S a), g ∈ mergeSet gates (S a) z)
    (hb : ∀ z ∈ zeroPts (S b), g ∈ mergeSet gates (S b) z) : False := by
  classical
  set z0 : Fin n → Bool := fun _ => false with hz0
  have h0 := mergeSet_subset_DT gates (S a) z0 (ha z0 (by simp [mem_zeroPts, hz0]))
  simp only [DT, Finset.mem_filter] at h0
  obtain ⟨-, -, u, v, huv, hu, hv, hgu, hgv⟩ := h0
  have key : ∀ x, val gates (upPt z0 x) g = true → x ∈ S b := by
    intro x hx
    by_contra hxb
    have hz : upPt z0 x ∈ zeroPts (S b) := by
      rw [mem_zeroPts]
      intro c hc
      have hne : c ≠ x := fun h => hxb (h ▸ hc)
      simp [upPt, Function.update_of_ne hne, hz0]
    have h1 := mergeSet_subset_DT gates (S b) _ (hb _ hz)
    simp only [DT, Finset.mem_filter] at h1
    rw [h1.2.1] at hx
    exact absurd hx (by simp)
  have h2 : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu, key _ hgu⟩
    · exact Finset.mem_inter.mpr ⟨hv, key _ hgv⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_pair huv] at h3
  have := hS a b hab
  omega

/-- **The single-price case of MergePrice** is proved: for a price concentrated on one gate
wire `g0` the price inequality holds (for every circuit, correct or not). -/
theorem mergePrice_single {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (gates : List Gate) (g0 : ℕ)
    (hg0 : g0 ∈ Finset.Ico n (n + gates.length)) (c : ℝ) (hc : 0 ≤ c) :
    ∑ w, (zeroPts (S w)).inf' (zeroPts_nonempty _)
        (fun z => ∑ g ∈ mergeSet gates (S w) z, (if g = g0 then c else 0))
      ≤ ∑ g ∈ Finset.Ico n (n + gates.length), (if g = g0 then c else 0) := by
  classical
  simp only [Finset.sum_ite_eq', hg0, ite_true]
  have hterm : ∀ w, (zeroPts (S w)).inf' (zeroPts_nonempty _)
      (fun z => if g0 ∈ mergeSet gates (S w) z then c else 0)
      ≤ if (∀ z ∈ zeroPts (S w), g0 ∈ mergeSet gates (S w) z) then c else 0 := by
    intro w
    split_ifs with h
    · obtain ⟨z, hz⟩ := zeroPts_nonempty (S w)
      refine (Finset.inf'_le _ hz).trans ?_
      split_ifs
      · exact le_rfl
      · exact hc
    · obtain ⟨z, hz⟩ := not_forall.mp h
      obtain ⟨hz1, hz2⟩ := Classical.not_imp.mp hz
      exact (Finset.inf'_le _ hz1).trans (by rw [ite_eq_right hz2])
  refine (Finset.sum_le_sum fun w _ => hterm w).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun w : Fin m =>
      ∀ z ∈ zeroPts (S w), g0 ∈ mergeSet gates (S w) z).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      by_contra hab
      rw [Finset.mem_filter] at ha hb
      exact univMerge_disjoint S hS gates a b hab g0 ha.2 hb.2
  have h1 : ((Finset.univ.filter fun w : Fin m =>
      ∀ z ∈ zeroPts (S w), g0 ∈ mergeSet gates (S w) z).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  nlinarith

/-! ## Level 4: cover-price form, charging principle, Theorem F -/

/-- Form (U), primal arithmetic (chist C2): entries `e` with counts `c e`, weights `y e`, and a
sub-selection `x e g` with `∑ g, x e g = c e * y e` and every item loaded at most once. Then
`∑ e, c e * y e ≤ #items`. (The constraints `0 ≤ x e g ≤ y e`, `x e g = 0` off the class of `e`
are not needed for the bound.) -/
theorem subselection_bound {ε α : Type*} [Fintype ε] [Fintype α] (c : ε → ℕ) (y : ε → ℝ)
    (x : ε → α → ℝ) (hsum : ∀ e, ∑ g, x e g = c e * y e) (hload : ∀ g, ∑ e, x e g ≤ 1) :
    ∑ e, (c e : ℝ) * y e ≤ Fintype.card α := by
  calc ∑ e, (c e : ℝ) * y e = ∑ e, ∑ g, x e g := Finset.sum_congr rfl fun e _ => (hsum e).symm
    _ = ∑ g, ∑ e, x e g := Finset.sum_comm
    _ ≤ ∑ _g : α, (1 : ℝ) := Finset.sum_le_sum fun g _ => hload g
    _ = Fintype.card α := by simp

/-- **Cover-price form** (dual of (U), on the test-system menu of the real circuit): every
nonnegative pricing that pays `|S w| - 1` on ANY `|S w| - 1` counted wires of EVERY test system
(i.e. on the cheapest ones) has total price at least the base. -/
def CoverPrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∀ π : ℕ → ℝ, (∀ g, 0 ≤ π g) →
    (∀ (w : Fin m) (σ : TestSys n gates (S w) (out w)) (A : Finset ℕ), A ⊆ σ.cnt →
      A.card = (S w).card - 1 → (((S w).card - 1 : ℕ) : ℝ) ≤ ∑ g ∈ A, π g) →
    ∑ w, (((S w).card - 1 : ℕ) : ℝ) ≤ ∑ g ∈ Finset.Ico n (n + gates.length), π g

/-- The cover-price form gives the bound (the all-ones pricing is always feasible). -/
theorem bound_of_coverPrice {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hp : CoverPrice S gates out) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  have h := hp (fun _ => 1) (fun _ => zero_le_one) (fun w σ A _ hA => by simp [hA])
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico, add_tsub_cancel_left] at h
  exact_mod_cast h

/-- **The cover-price form on minimal counterexamples closes 951.** -/
theorem no_minCE_of_coverPrice
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → CoverPrice S gates out) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  fun {n m} S gates out M => by
    have h1 := bound_of_coverPrice S gates out (H n m S gates out M)
    have h2 := M.ce.hlt
    omega

/-- The cover-price form is weaker than `PriceIneq` (= `FracMatch`), with the same conclusion. -/
theorem coverPrice_of_priceIneq {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hp : PriceIneq S gates out) : CoverPrice S gates out := by
  intro π hπ hcov
  obtain ⟨σ, M, hsub, hcard, h⟩ := hp π hπ
  exact (Finset.sum_le_sum fun w _ => hcov w (σ w) (M w) (hsub w) (hcard w)).trans h

/-- MergeFrac ⇒ cover-price form. -/
theorem coverPrice_of_mergeFrac {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hf : MergeFrac S gates) : CoverPrice S gates out :=
  coverPrice_of_priceIneq S gates out
    ((fracMatch_iff_priceIneq S gates out).1 (fracMatch_of_mergeFrac S gates out hg hU hev hf))

section TheoremF

variable {N : ℕ} {ι : Type*}

/-- A set `T` of entries (zero sets `Z e`, atoms `a e`) is **servable**: every entry of `T` has
at least two atoms that lie below no point of `⋃ e' ∈ T, Z e'`. -/
def Servable (k : ι → ℕ) (Z : ι → Finset (Fin N → Bool)) (a : ∀ e, Fin (k e) → Fin N → Bool)
    (T : Finset ι) : Prop :=
  ∀ e ∈ T, 1 < (Finset.univ.filter fun t : Fin (k e) =>
    ∀ e' ∈ T, ∀ y ∈ Z e', ¬ a e t ≤ y).card

/-- **Lemma R**: on a monotone circuit, the entries whose class contains a given gate form a
servable set (the gate is `0` on every `Z e'` and `1` at two atoms of each entry). -/
theorem servable_of_gate (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (k : ι → ℕ) (Z : ι → Finset (Fin N → Bool)) (a : ∀ e, Fin (k e) → Fin N → Bool) (j : ℕ)
    (T : Finset ι) (hT : ∀ e ∈ T, j ∈ liftCl gs (Z e) (a e)) : Servable k Z a T := by
  classical
  intro e he
  obtain ⟨-, -, hc⟩ := mem_liftCl.mp (hT e he)
  refine lt_of_lt_of_le hc (Finset.card_le_card fun t ht => ?_)
  rw [mem_atomsAt] at ht
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun e' he' y hy hle => ?_⟩
  have h1 := Bool.le_iff_imp.mp (val_le_of_le gs hg hle (N + j)) ht
  rw [(mem_liftCl.mp (hT e' he')).2.1 y hy] at h1
  exact absurd h1 (by simp)

/-- **Theorem F, monotone core** (fractional X+ family bound). `gs` a monotone list; entries
`e` (wire `o e`, nonempty join-closed zero set `Z e`, `k e` atoms, S2.1 hypotheses); weights
`y ≥ 0` with `y(T) ≤ 1` for every servable `T`. Then `∑ e, y e * (k e - 1) ≤ gs.length`. -/
theorem servablePacking_mono [Fintype ι] (gs : List Gate) (hm : MonoList gs) (k : ι → ℕ)
    (Z : ι → Finset (Fin N → Bool)) (a : ∀ e, Fin (k e) → Fin N → Bool) (o : ι → ℕ)
    (hZ : ∀ e, (Z e).Nonempty) (hjoin : ∀ e, ∀ x ∈ Z e, ∀ y ∈ Z e, x ⊔ y ∈ Z e)
    (hL : ∀ e, ∀ c : Fin N, (∀ x ∈ Z e, x c = false) →
      ∀ s t, a e s c = true → a e t c = true → s = t)
    (hZo : ∀ e, ∀ x ∈ Z e, val gs x (o e) = false) (hao : ∀ e t, val gs (a e t) (o e) = true)
    (y : ι → ℝ) (hy0 : ∀ e, 0 ≤ y e)
    (hy : ∀ T : Finset ι, Servable k Z a T → ∑ e ∈ T, y e ≤ 1) :
    ∑ e, y e * ((k e - 1 : ℕ) : ℝ) ≤ gs.length := by
  classical
  have hload : ∀ g : ℕ, ∑ e, (if g ∈ liftClOr gs (Z e) (a e) then y e else 0) ≤ 1 := by
    intro g
    rw [← Finset.sum_filter]
    exact hy _ (servable_of_gate gs hm.andOr k Z a g _ fun e he =>
      liftClOr_subset gs (Z e) (a e) (Finset.mem_filter.mp he).2)
  have h1 := sum_mul_card_le_card_biUnion Finset.univ y (fun e => liftClOr gs (Z e) (a e)) hload
  have h2 : (Finset.univ.biUnion fun e : ι => liftClOr gs (Z e) (a e)).card ≤ gs.length := by
    have hsub : (Finset.univ.biUnion fun e : ι => liftClOr gs (Z e) (a e)) ⊆
        Finset.range gs.length := by
      intro g hg
      obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp hg
      exact Finset.mem_range.mpr (mem_liftClOr.mp he).1
    simpa using Finset.card_le_card hsub
  calc ∑ e, y e * ((k e - 1 : ℕ) : ℝ)
      ≤ ∑ e, y e * ((liftClOr gs (Z e) (a e)).card : ℝ) :=
        Finset.sum_le_sum fun e _ => by
          have hc := lift_count gs hm (Z e) (hZ e) (hjoin e) (a e) (hL e) (o e) (hZo e) (hao e)
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (hy0 e)
    _ ≤ _ := h1
    _ ≤ gs.length := by exact_mod_cast h2

end TheoremF

/-- **Theorem F** (`s ≥ 1 + V_fun`): one NOT gate (position `p`); any family of entries of the
lifted circuit (wire `o e`, nonempty join-closed zero set, `k e` atoms, S2.1 hypotheses) and any
weights `y ≥ 0` with `y(T) ≤ 1` on every servable set `T` give
`∑ e, y e * (k e - 1) ≤ gates.length - 1`. Servability and the entry hypotheses mention only the
values of the lifted output wires, so the left side is the function-level packing value. -/
theorem bound_of_servablePacking {n : ℕ} {ι : Type*} [Fintype ι] (gates : List Gate) (p : ℕ)
    (hp : p < gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not) (k : ι → ℕ)
    (Z : ι → Finset (Fin (n + 1) → Bool)) (a : ∀ e, Fin (k e) → Fin (n + 1) → Bool)
    (o : ι → ℕ)
    (hZ : ∀ e, (Z e).Nonempty) (hjoin : ∀ e, ∀ x ∈ Z e, ∀ y ∈ Z e, x ⊔ y ∈ Z e)
    (hL : ∀ e, ∀ c : Fin (n + 1), (∀ x ∈ Z e, x c = false) →
      ∀ s t, a e s c = true → a e t c = true → s = t)
    (hZo : ∀ e, ∀ x ∈ Z e, val (lift n p gates) x (o e) = false)
    (hao : ∀ e t, val (lift n p gates) (a e t) (o e) = true)
    (y : ι → ℝ) (hy0 : ∀ e, 0 ≤ y e)
    (hy : ∀ T : Finset ι, Servable k Z a T → ∑ e ∈ T, y e ≤ 1) :
    ∑ e, y e * ((k e - 1 : ℕ) : ℝ) ≤ ((gates.length - 1 : ℕ) : ℝ) := by
  have h := servablePacking_mono (lift n p gates) (lift_ops gates p hp hg hU hN) k Z a o hZ hjoin
    hL hZo hao y hy0 hy
  rwa [length_lift n p gates hp] at h

/-- **Theorem F on counterexamples** (the minimality fact "`V_fun < base`" of chist C3, in the
sharper form `V_fun ≤ base - 2`): in a counterexample with its NOT gate at `p`, every servable
packing of entries of the lifted circuit has value at most `base - 2`. So a function-level packing
of value `≥ base - 1` rules out every counterexample with that NOT input. -/
theorem IsCE.servablePacking_le {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (C : IsCE S gates out) {ι : Type*} [Fintype ι] (p : ℕ)
    (hp : p < gates.length) (hN : (gates[p]'hp).op = GateOp.not) (k : ι → ℕ)
    (Z : ι → Finset (Fin (n + 1) → Bool)) (a : ∀ e, Fin (k e) → Fin (n + 1) → Bool)
    (o : ι → ℕ)
    (hZ : ∀ e, (Z e).Nonempty) (hjoin : ∀ e, ∀ x ∈ Z e, ∀ y ∈ Z e, x ⊔ y ∈ Z e)
    (hL : ∀ e, ∀ c : Fin (n + 1), (∀ x ∈ Z e, x c = false) →
      ∀ s t, a e s c = true → a e t c = true → s = t)
    (hZo : ∀ e, ∀ x ∈ Z e, val (lift n p gates) x (o e) = false)
    (hao : ∀ e t, val (lift n p gates) (a e t) (o e) = true)
    (y : ι → ℝ) (hy0 : ∀ e, 0 ≤ y e)
    (hy : ∀ T : Finset ι, Servable k Z a T → ∑ e ∈ T, y e ≤ 1) :
    ∑ e, y e * ((k e - 1 : ℕ) : ℝ) + 2 ≤ ((∑ i : Fin m, ((S i).card - 1) : ℕ) : ℝ) := by
  have h := bound_of_servablePacking gates p hp C.hg C.hU hN k Z a o hZ hjoin hL hZo hao y hy0
    hy
  have hlt := C.hlt
  have h1 : gates.length - 1 + 2 ≤ ∑ i : Fin m, ((S i).card - 1) := by omega
  have h2 : ((gates.length - 1 : ℕ) : ℝ) + 2 ≤ ((∑ i : Fin m, ((S i).card - 1) : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

end PEqualNP.Outside.L_meta_951_aux
