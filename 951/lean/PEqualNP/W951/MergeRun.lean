import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Count
import PEqualNP.W951.MergeRunT

-- The union-find run behind `main_inv`, made explicit.
-- `runL Q R gs k` is the labelling after the first k gates, `runM Q R gs k` the set of
-- wire indices n + j (j < k) at which a merge happened. A merge at gate j happens exactly
-- when wire n + j is tracked (false at Zof Q) and its trace within R meets at least two
-- classes of the current labelling; then all those classes are sent to one fixed member
-- (`mrep`, the min' of the classes met). Main results: `merge_run`, `merge_count`.
-- This is the instance `z = Zof Q`, `p = eof` of the generic run in MergeRunT.lean (which
-- also holds `mrep`, `mr_val_*`, `mr_split`, `mr_card_img_le_one`); everything here is derived.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The trace of wire `i` within `R`. -/
def trR {n : ℕ} (R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  R.filter fun u => val gs (eof u) i = true

/-- Gate `j` merges under labelling `l`. -/
def Mg {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) : Prop :=
  val gs (Zof Q) (n + j) = false ∧ 1 < ((trR R gs (n + j)).image l).card

instance {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) :
    Decidable (Mg Q R gs l j) := inferInstanceAs (Decidable (MgT (Zof Q) eof R gs l j))

/-- One step of the run. -/
def mstep {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) :
    Fin n → Fin n := mstepT (Zof Q) eof R gs l j

/-- (M1) Labelling after the first `k` gates. -/
def runL {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) : ℕ → Fin n → Fin n :=
  runLT (Zof Q) eof R gs

/-- (M1) Merge set after the first `k` gates. -/
def runM {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) : ℕ → Finset ℕ :=
  runMT (Zof Q) eof R gs

/-- Invariant (M2) at prefix length `k`. -/
def InvK {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (k : ℕ) (l : Fin n → Fin n) : Prop :=
  InvKT (Zof Q) eof R gs k l

section

variable {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate)

theorem eof_hT : ∀ u ∈ R, ∀ c : Fin n, eof u c = true → Zof Q c = false → c = u := by
  intro u _ c h _
  simpa [eof] using h

theorem good_goodT (hgood : Good Q gs) : GoodT (Zof Q) eof R gs := by
  intro pre g rest h
  rcases hgood pre g rest h with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr fun u _ v _ hu _ => by rw [h1 u] at hu; exact absurd hu (by simp))

/-- A tracked wire's trace is covered by the traces of at most two earlier tracked wires. -/
theorem mr_cover (hgood : Good Q gs) (k : ℕ) (hz : val gs (Zof Q) (n + k) = false) :
    ∃ a b : ℕ, ∀ u : Fin n, val gs (eof u) (n + k) = true →
      (a < n + k ∧ val gs (Zof Q) a = false ∧ val gs (eof u) a = true) ∨
      (b < n + k ∧ val gs (Zof Q) b = false ∧ val gs (eof u) b = true) :=
  (mr_coverG (Zof Q) eof gs (fun pre g => ∀ u : Fin n, g.op.eval
      (g.inputs.map fun j => val pre (eof u) j) = false) _ hgood k hz
    fun hk h => ⟨0, 0, fun u hu => by
      rw [mr_val_gate gs _ k hk, h u] at hu; exact absurd hu (by simp)⟩).elim id id

theorem mstep_comp (l : Fin n → Fin n) (j : ℕ) :
    ∃ φ : Fin n → Fin n, mstep Q R gs l j = φ ∘ l := mstepT_comp _ _ R gs l j

theorem mstep_apply {l : Fin n → Fin n} {j : ℕ} (hm : Mg Q R gs l j) (u : Fin n) :
    mstep Q R gs l j u =
      if l u ∈ (trR R gs (n + j)).image l then mrep _ hm.2 else l u :=
  mstepT_apply _ _ R gs hm u

theorem mstep_merge {l : Fin n → Fin n} {j : ℕ} (hm : Mg Q R gs l j) (u : Fin n)
    (hu : u ∈ trR R gs (n + j)) : mstep Q R gs l j u = mrep _ hm.2 :=
  mstepT_merge _ _ R gs hm u hu

theorem mstep_nomerge {l : Fin n → Fin n} {j : ℕ} (hm : ¬ Mg Q R gs l j) :
    mstep Q R gs l j = l := mstepT_nomerge _ _ R gs hm

theorem runL_succ (k : ℕ) : runL Q R gs (k + 1) = mstep Q R gs (runL Q R gs k) k := rfl

theorem invK_zero (l : Fin n → Fin n) : InvK Q R gs 0 l :=
  invKT_zero _ _ R gs (eof_hT Q R) l

theorem invK_succ (l : Fin n → Fin n) (k : ℕ) (h : InvK Q R gs k l) :
    InvK Q R gs (k + 1) (mstep Q R gs l k) := invKT_succ _ _ R gs l k h

theorem runL_inv (k : ℕ) : InvK Q R gs k (runL Q R gs k) :=
  runLT_inv _ _ R gs (eof_hT Q R) k

/-- A tracked wire's trace meets at most two classes. -/
theorem img_le_two (hgood : Good Q gs) (l : Fin n → Fin n) (k : ℕ) (h : InvK Q R gs k l)
    (hz : val gs (Zof Q) (n + k) = false) :
    ((trR R gs (n + k)).image l).card ≤ 2 :=
  img_le_twoT _ _ R gs (good_goodT Q R gs hgood) l k h hz

theorem img_merge (l : Fin n → Fin n) (k : ℕ) (hm : Mg Q R gs l k)
    (h2 : ((trR R gs (n + k)).image l).card ≤ 2) :
    (R.image l).card ≤ (R.image (mstep Q R gs l k)).card + 1 :=
  img_mergeT _ _ R gs l k hm h2

theorem runM_mem (k i : ℕ) :
    i ∈ runM Q R gs k ↔ ∃ j < k, i = n + j ∧ Mg Q R gs (runL Q R gs j) j :=
  runMT_mem _ _ R gs k i

theorem runM_mono (k K : ℕ) (h : k ≤ K) : runM Q R gs k ⊆ runM Q R gs K :=
  runMT_mono _ _ R gs k K h

/-- (M3) -/
theorem run_count (hgood : Good Q gs) (k : ℕ) :
    R.card ≤ (R.image (runL Q R gs k)).card + (runM Q R gs k).card :=
  run_countT _ _ R gs (eof_hT Q R) (good_goodT Q R gs hgood) k

/-- (M4) -/
theorem run_sub_D (k : ℕ) : runM Q R gs k ⊆ D Q R gs := run_sub_DT _ _ R gs k

/-- (M4) -/
theorem run_index (k i : ℕ) (hi : i ∈ runM Q R gs k) : ∃ j < k, i = n + j :=
  run_indexT _ _ R gs k i hi

/-- (M5) -/
theorem run_record (k j : ℕ) (hj : n + j ∈ runM Q R gs k) :
    (∃ u ∈ R, ∃ v ∈ R, val gs (eof u) (n + j) = true ∧ val gs (eof v) (n + j) = true ∧
        runL Q R gs j u ≠ runL Q R gs j v) ∧
      ∀ u ∈ R, ∀ v ∈ R, val gs (eof u) (n + j) = true → val gs (eof v) (n + j) = true →
        runL Q R gs (j + 1) u = runL Q R gs (j + 1) v :=
  run_recordT _ _ R gs k j hj

/-- (M6) -/
theorem run_persist (j k : ℕ) (u v : Fin n) (hjk : j ≤ k)
    (h : runL Q R gs j u = runL Q R gs j v) : runL Q R gs k u = runL Q R gs k v :=
  run_persistT _ _ R gs j k u v hjk h

/-- (M7), strong form: once `u, v` share a class after step `j`, no later gate whose
trace within `R` lies in `{u, v}` merges. -/
theorem run_once (k j j' : ℕ) (u v : Fin n)
    (hj : runL Q R gs (j + 1) u = runL Q R gs (j + 1) v) (hjj : j < j')
    (htr : ∀ w ∈ R, val gs (eof w) (n + j') = true → w = u ∨ w = v) :
    n + j' ∉ runM Q R gs k := run_onceT _ _ R gs k j j' u v hj hjj htr

/-- (M2) for the full list, in the form of `Inv`. -/
theorem run_Inv (hgood : Good Q gs) : Inv Q R gs (runL Q R gs gs.length) := by
  obtain ⟨l0, hinv0, -⟩ := main_inv Q R gs hgood
  intro i u v hz hu hv
  exact ⟨(hinv0 i u v hz hu hv).1, fun huR hvR =>
    run_InvT _ _ R gs (eof_hT Q R) i u v hz hu hv huR hvR⟩

/-- (M8) The explicit union-find run, packaged. -/
theorem merge_run (hgood : Good Q gs) :
    ∃ (L : ℕ → Fin n → Fin n) (M : ℕ → Finset ℕ),
      L 0 = id ∧ M 0 = ∅ ∧
      -- (M2)
      (∀ k, ∀ i < n + k, val gs (Zof Q) i = false → ∀ u ∈ R, ∀ v ∈ R,
        val gs (eof u) i = true → val gs (eof v) i = true → L k u = L k v) ∧
      (∀ i u, val gs (Zof Q) i = false → val gs (eof u) i = true → u ∈ Q) ∧
      Inv Q R gs (L gs.length) ∧
      -- (M3)
      (∀ k, R.card ≤ (R.image (L k)).card + (M k).card) ∧
      -- (M4)
      (∀ k, M k ⊆ D Q R gs) ∧ (∀ k, ∀ i ∈ M k, ∃ j < k, i = n + j) ∧
      (∀ k K, k ≤ K → M k ⊆ M K) ∧
      -- (M5)
      (∀ k j, n + j ∈ M k →
        (∃ u ∈ R, ∃ v ∈ R, val gs (eof u) (n + j) = true ∧ val gs (eof v) (n + j) = true ∧
          L j u ≠ L j v) ∧
        ∀ u ∈ R, ∀ v ∈ R, val gs (eof u) (n + j) = true → val gs (eof v) (n + j) = true →
          L (j + 1) u = L (j + 1) v) ∧
      -- (M6)
      (∀ j k u v, j ≤ k → L j u = L j v → L k u = L k v) ∧
      -- (M7)
      (∀ k j j' u v, u ∈ R → v ∈ R → L j u ≠ L j v → L (j + 1) u = L (j + 1) v → j < j' →
        (∀ w ∈ R, val gs (eof w) (n + j') = true → w = u ∨ w = v) → n + j' ∉ M k) := by
  obtain ⟨l0, hinv0, -⟩ := main_inv Q R gs hgood
  exact ⟨runL Q R gs, runM Q R gs, rfl, rfl, fun k => runL_inv Q R gs k,
    fun i u hz hu => (hinv0 i u u hz hu hu).1, run_Inv Q R gs hgood,
    run_count Q R gs hgood, run_sub_D Q R gs, run_index Q R gs, runM_mono Q R gs,
    run_record Q R gs, run_persist Q R gs,
    fun k j j' u v _ _ _ hj hjj htr => run_once Q R gs k j j' u v hj hjj htr⟩

/-- (M8) Corollary, mirroring `count_world`: one merge per extra element of `R`. -/
theorem merge_count (hgood : Good Q gs) (o : ℕ) (hz : val gs (Zof Q) o = false)
    (hu : ∀ u ∈ R, val gs (eof u) o = true) :
    R.card - 1 ≤ (runM Q R gs gs.length).card :=
  merge_countT _ _ R gs (eof_hT Q R) (good_goodT Q R gs hgood) o hz hu

end

end PEqualNP.Outside.L_meta_951_aux
