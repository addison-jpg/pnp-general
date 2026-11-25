import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Eval
import PEqualNP.Kernel.W951Core

-- The explicit union-find run, for general test systems (MergeRun.lean specialises it to
-- `z = Zof Q`, `p = eof`)
-- (zero point `z`, test points `p u`, as in Frame.lean / GapG.lean).
-- `runLT z p R gs k` is the labelling after the first k gates, `runMT z p R gs k` the merge set.
-- A merge at gate j happens exactly when wire n + j is false at `z` and its trace
-- {u ∈ R : val gs (p u) (n + j) = true} meets at least two classes of the current labelling;
-- those classes are sent to their `min'`. Main results: `merge_runT`, `merge_countT`.
-- This is the one proof of the union-find invariant: `Count.main_invT` is its corollary, and
-- `TestSys.merges` (MergeRunTSys.lean) its per-test-system form.

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Counting with general test systems (zero point `z`, test points `p u`) -/

/-- Each gate is AND/OR, or true at the zero point, or true at the test points of at most one
element of `R`. -/
def GoodT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (rest : List Gate), gs = pre ++ g :: rest →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
      g.op.eval (g.inputs.map fun j => val pre z j) = true ∨
      ∀ u ∈ R, ∀ v ∈ R, g.op.eval (g.inputs.map fun j => val pre (p u) j) = true →
        g.op.eval (g.inputs.map fun j => val pre (p v) j) = true → u = v

def InvT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs z i = false → val gs (p u) i = true → val gs (p v) i = true →
    u ∈ R → v ∈ R → l u = l v

def CntT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (i : ℕ) : Prop :=
  val gs z i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ u ∈ R ∧ v ∈ R ∧ val gs (p u) i = true ∧ val gs (p v) i = true

open Classical in
noncomputable def DT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => CntT z p R gs i

theorem DT_mono {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (g : Gate) : DT z p R gs ⊆ DT z p R (gs ++ [g]) := by
  classical
  intro i hi
  simp only [DT, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, huR, hvR, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, huR, hvR, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

/-- The trace of wire `i` within `R`, for test points `p`. -/
def trRT {n : ℕ} (p : Fin n → Fin n → Bool) (R : Finset (Fin n)) (gs : List Gate) (i : ℕ) :
    Finset (Fin n) :=
  R.filter fun u => val gs (p u) i = true

/-- Gate `j` merges under labelling `l`. -/
def MgT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) : Prop :=
  val gs z (n + j) = false ∧ 1 < ((trRT p R gs (n + j)).image l).card

instance {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) : Decidable (MgT z p R gs l j) := by
  unfold MgT; infer_instance

/-- The representative class of a merge. -/
def mrep {n : ℕ} (S : Finset (Fin n)) (h : 1 < S.card) : Fin n :=
  S.min' (Finset.card_pos.mp (by omega))

/-- One step of the run. -/
def mstepT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (l : Fin n → Fin n) (j : ℕ) : Fin n → Fin n :=
  if h : MgT z p R gs l j then
    fun u => if l u ∈ (trRT p R gs (n + j)).image l then mrep _ h.2 else l u
  else l

/-- Labelling after the first `k` gates. -/
def runLT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) : ℕ → Fin n → Fin n
  | 0 => id
  | k + 1 => mstepT z p R gs (runLT z p R gs k) k

/-- Merge set after the first `k` gates. -/
def runMT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) : ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 => if MgT z p R gs (runLT z p R gs k) k then insert (n + k) (runMT z p R gs k)
      else runMT z p R gs k

/-- Invariant at prefix length `k`. -/
def InvKT {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
    (gs : List Gate) (k : ℕ) (l : Fin n → Fin n) : Prop :=
  ∀ i, i < n + k → val gs z i = false → ∀ u ∈ R, ∀ v ∈ R,
    val gs (p u) i = true → val gs (p v) i = true → l u = l v

section

variable {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (R : Finset (Fin n))
  (gs : List Gate)

theorem mr_val_ge (x : Fin n → Bool) (i : ℕ) (h : n + gs.length ≤ i) :
    val gs x i = false :=
  PEqualNP.Kernel.listVal_ge gs x i h

theorem mr_val_take (x : Fin n → Bool) (k i : ℕ) (hi : i < n + k) :
    val gs x i = val (gs.take k) x i := by
  by_cases hk : k ≤ gs.length
  · conv_lhs => rw [← List.take_append_drop k gs]
    exact val_append _ _ x i (by rw [List.length_take, Nat.min_eq_left hk]; omega)
  · rw [List.take_of_length_le (by omega)]

theorem mr_val_gate (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    val gs x (n + k) = gs[k].op.eval (gs[k].inputs.map fun j => val (gs.take k) x j) :=
  PEqualNP.Kernel.listVal_gate gs x k hk

theorem mr_split (k : ℕ) (hk : k < gs.length) :
    gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
  conv_lhs => rw [← List.take_append_drop k gs]
  rw [List.drop_eq_getElem_cons hk]

theorem mr_card_img_le_one (l : Fin n → Fin n) (p : Fin n → Prop) [DecidablePred p]
    (h : ∀ u ∈ R, ∀ v ∈ R, p u → p v → l u = l v) : ((R.filter p).image l).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_filter] at hu hv
  exact h u hu.1 v hv.1 hu.2 hv.2

/-- Generic cover lemma: if every gate is AND/OR of fan-in at most 2, or true at `z`, or satisfies
`X`, and `X` at the gate yields `Y`, then `Y` holds or the trace of a tracked wire is covered by
the traces of at most two earlier tracked wires. -/
theorem mr_coverG (X : List Gate → Gate → Prop) (Y : Prop)
    (hgood : ∀ (pre : List Gate) (g : Gate) (rest : List Gate), gs = pre ++ g :: rest →
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
        g.op.eval (g.inputs.map fun j => val pre z j) = true ∨ X pre g)
    (k : ℕ) (hz : val gs z (n + k) = false)
    (hX : ∀ hk : k < gs.length, X (gs.take k) gs[k] → Y) :
    Y ∨ ∃ a b : ℕ, ∀ u : Fin n, val gs (p u) (n + k) = true →
      (a < n + k ∧ val gs z a = false ∧ val gs (p u) a = true) ∨
      (b < n + k ∧ val gs z b = false ∧ val gs (p u) b = true) := by
  by_cases hk : k < gs.length
  swap
  · refine Or.inr ⟨0, 0, fun u hu => ?_⟩
    rw [mr_val_ge gs _ _ (by omega)] at hu
    exact absurd hu (by simp)
  have hg := hgood _ _ _ (mr_split gs k hk)
  have hv := mr_val_gate (n := n) gs
  have conv : ∀ (x : Fin n → Bool) i,
      val (gs.take k) x i = true → i < n + k ∧ val gs x i = true := by
    intro x i h
    by_cases hi : i < n + k
    · exact ⟨hi, by rw [mr_val_take gs x k i hi]; exact h⟩
    · rw [mr_val_ge _ x i (by rw [List.length_take, Nat.min_eq_left hk.le]; omega)] at h
      exact absurd h (by simp)
  have convz : ∀ i, i < n + k → val (gs.take k) z i = false → val gs z i = false := by
    intro i hi h
    rw [mr_val_take gs _ k i hi]; exact h
  rcases hg with ⟨hop, hlen⟩ | h | h
  · right
    rcases gate_cases gs[k] hop hlen (fun x j => val (gs.take k) x j) z with
      hall | ⟨a, b, hab⟩
    · refine ⟨0, 0, fun u hu => ?_⟩
      rw [hv _ k hk, hall] at hu
      exact absurd hu (by simp)
    · rw [hv _ k hk] at hz
      obtain ⟨ha, hb, hy⟩ := hab hz
      refine ⟨a, b, fun u hu => ?_⟩
      rw [hv _ k hk] at hu
      rcases hy (p u) hu with h | h
      · obtain ⟨h1, h2⟩ := conv _ _ h
        exact Or.inl ⟨h1, convz a h1 ha, h2⟩
      · obtain ⟨h1, h2⟩ := conv _ _ h
        exact Or.inr ⟨h1, convz b h1 hb, h2⟩
  · rw [hv _ k hk] at hz
    rw [hz] at h
    exact absurd h (by simp)
  · exact Or.inl (hX hk h)

/-- A tracked wire's trace within `R` is a single point, or covered by the traces of at most
two earlier tracked wires. -/
theorem mr_coverT (hgood : GoodT z p R gs) (k : ℕ) (hz : val gs z (n + k) = false) :
    (∀ u ∈ R, ∀ v ∈ R, val gs (p u) (n + k) = true → val gs (p v) (n + k) = true → u = v) ∨
    ∃ a b : ℕ, ∀ u : Fin n, val gs (p u) (n + k) = true →
      (a < n + k ∧ val gs z a = false ∧ val gs (p u) a = true) ∨
      (b < n + k ∧ val gs z b = false ∧ val gs (p u) b = true) :=
  mr_coverG z p gs
    (fun pre g => ∀ u ∈ R, ∀ v ∈ R, g.op.eval (g.inputs.map fun j => val pre (p u) j) = true →
      g.op.eval (g.inputs.map fun j => val pre (p v) j) = true → u = v) _ hgood k hz
    fun hk h u hu v hv' hpu hpv => by
      rw [mr_val_gate gs _ k hk] at hpu hpv
      exact h u hu v hv' hpu hpv

theorem mstepT_comp (l : Fin n → Fin n) (j : ℕ) :
    ∃ φ : Fin n → Fin n, mstepT z p R gs l j = φ ∘ l := by
  unfold mstepT
  split_ifs with h
  · exact ⟨fun y => if y ∈ (trRT p R gs (n + j)).image l then mrep _ h.2 else y, rfl⟩
  · exact ⟨id, rfl⟩

theorem mstepT_apply {l : Fin n → Fin n} {j : ℕ} (hm : MgT z p R gs l j) (u : Fin n) :
    mstepT z p R gs l j u =
      if l u ∈ (trRT p R gs (n + j)).image l then mrep _ hm.2 else l u := by
  unfold mstepT
  rw [dite_eq_left hm]

theorem mstepT_merge {l : Fin n → Fin n} {j : ℕ} (hm : MgT z p R gs l j) (u : Fin n)
    (hu : u ∈ trRT p R gs (n + j)) : mstepT z p R gs l j u = mrep _ hm.2 := by
  rw [mstepT_apply z p R gs hm, ite_eq_left (Finset.mem_image_of_mem l hu)]

theorem mstepT_nomerge {l : Fin n → Fin n} {j : ℕ} (hm : ¬ MgT z p R gs l j) :
    mstepT z p R gs l j = l := by
  unfold mstepT
  rw [dite_eq_right hm]

theorem runLT_succ (k : ℕ) :
    runLT z p R gs (k + 1) = mstepT z p R gs (runLT z p R gs k) k := rfl

theorem invKT_zero (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (l : Fin n → Fin n) : InvKT z p R gs 0 l := by
  intro i hi hz u hu v hv hui hvi
  rw [mr_val_take gs _ 0 i hi, List.take_zero, val_nil, dite_eq_left (by omega)]
    at hui hvi hz
  rw [← hT u hu _ hui hz, ← hT v hv _ hvi hz]

theorem invKT_succ (l : Fin n → Fin n) (k : ℕ) (h : InvKT z p R gs k l) :
    InvKT z p R gs (k + 1) (mstepT z p R gs l k) := by
  intro i hi hz u hu v hv hui hvi
  by_cases hik : i < n + k
  · obtain ⟨φ, hφ⟩ := mstepT_comp z p R gs l k
    rw [hφ]
    show φ (l u) = φ (l v)
    rw [h i hik hz u hu v hv hui hvi]
  · have hi' : i = n + k := by omega
    subst hi'
    have huT : u ∈ trRT p R gs (n + k) := Finset.mem_filter.mpr ⟨hu, hui⟩
    have hvT : v ∈ trRT p R gs (n + k) := Finset.mem_filter.mpr ⟨hv, hvi⟩
    by_cases hm : MgT z p R gs l k
    · rw [mstepT_merge z p R gs hm u huT, mstepT_merge z p R gs hm v hvT]
    · rw [mstepT_nomerge z p R gs hm]
      have hc : ((trRT p R gs (n + k)).image l).card ≤ 1 := by
        by_contra hc
        exact hm ⟨hz, by omega⟩
      exact Finset.card_le_one.mp hc _ (Finset.mem_image_of_mem l huT) _
        (Finset.mem_image_of_mem l hvT)

theorem runLT_inv (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (k : ℕ) : InvKT z p R gs k (runLT z p R gs k) := by
  induction k with
  | zero => exact invKT_zero z p R gs hT _
  | succ k ih => exact invKT_succ z p R gs _ k ih

/-- A tracked wire's trace meets at most two classes. -/
theorem img_le_twoT (hgood : GoodT z p R gs) (l : Fin n → Fin n) (k : ℕ)
    (h : InvKT z p R gs k l) (hz : val gs z (n + k) = false) :
    ((trRT p R gs (n + k)).image l).card ≤ 2 := by
  rcases mr_coverT z p R gs hgood k hz with h1 | ⟨a, b, hab⟩
  · have : ((trRT p R gs (n + k)).image l).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      rw [trRT, Finset.mem_filter] at hu hv
      rw [h1 u hu.1 v hv.1 hu.2 hv.2]
    omega
  have hA := mr_card_img_le_one R l
    (fun u => a < n + k ∧ val gs z a = false ∧ val gs (p u) a = true)
    (fun u hu v hv pu pv => h a pu.1 pu.2.1 u hu v hv pu.2.2 pv.2.2)
  have hB := mr_card_img_le_one R l
    (fun u => b < n + k ∧ val gs z b = false ∧ val gs (p u) b = true)
    (fun u hu v hv pu pv => h b pu.1 pu.2.1 u hu v hv pu.2.2 pv.2.2)
  have hsub : (trRT p R gs (n + k)).image l ⊆
      (R.filter fun u => a < n + k ∧ val gs z a = false ∧ val gs (p u) a = true).image l
      ∪ (R.filter fun u => b < n + k ∧ val gs z b = false ∧ val gs (p u) b = true).image l := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rw [trRT, Finset.mem_filter] at hu
    rcases hab u hu.2 with h1 | h1
    · exact Finset.mem_union_left _
        (Finset.mem_image_of_mem l (Finset.mem_filter.mpr ⟨hu.1, h1⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_image_of_mem l (Finset.mem_filter.mpr ⟨hu.1, h1⟩))
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem img_mergeT (l : Fin n → Fin n) (k : ℕ) (hm : MgT z p R gs l k)
    (h2 : ((trRT p R gs (n + k)).image l).card ≤ 2) :
    (R.image l).card ≤ (R.image (mstepT z p R gs l k)).card + 1 := by
  have hr : mrep _ hm.2 ∈ (trRT p R gs (n + k)).image l := Finset.min'_mem _ _
  have hsub : R.image l ⊆ R.image (mstepT z p R gs l k) ∪
      ((trRT p R gs (n + k)).image l).erase (mrep _ hm.2) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    by_cases hyS : l w ∈ (trRT p R gs (n + k)).image l
    · by_cases hyr : l w = mrep _ hm.2
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
        rw [mstepT_apply z p R gs hm, ite_eq_left hyS, hyr]
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hyr, hyS⟩)
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
      rw [mstepT_apply z p R gs hm, ite_eq_right hyS]
  have h1 := Finset.card_le_card hsub
  have h3 := Finset.card_union_le (R.image (mstepT z p R gs l k))
    (((trRT p R gs (n + k)).image l).erase (mrep _ hm.2))
  have h4 := Finset.card_erase_of_mem hr
  omega

theorem runMT_mem (k i : ℕ) :
    i ∈ runMT z p R gs k ↔ ∃ j < k, i = n + j ∧ MgT z p R gs (runLT z p R gs j) j := by
  induction k with
  | zero => simp [runMT]
  | succ k ih =>
    rw [runMT]
    split_ifs with hm
    · rw [Finset.mem_insert, ih]
      constructor
      · rintro (rfl | ⟨j, hj, rfl, hj'⟩)
        · exact ⟨k, by omega, rfl, hm⟩
        · exact ⟨j, by omega, rfl, hj'⟩
      · rintro ⟨j, hj, rfl, hj'⟩
        by_cases hjk : j = k
        · left; rw [hjk]
        · right; exact ⟨j, by omega, rfl, hj'⟩
    · rw [ih]
      constructor
      · rintro ⟨j, hj, rfl, hj'⟩
        exact ⟨j, by omega, rfl, hj'⟩
      · rintro ⟨j, hj, rfl, hj'⟩
        by_cases hjk : j = k
        · subst hjk; exact absurd hj' hm
        · exact ⟨j, by omega, rfl, hj'⟩

theorem runMT_mono (k K : ℕ) (h : k ≤ K) : runMT z p R gs k ⊆ runMT z p R gs K := by
  intro i hi
  obtain ⟨j, hj, he, hm⟩ := (runMT_mem z p R gs k i).mp hi
  exact (runMT_mem z p R gs K i).mpr ⟨j, by omega, he, hm⟩

theorem run_countT (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (hgood : GoodT z p R gs) (k : ℕ) :
    R.card ≤ (R.image (runLT z p R gs k)).card + (runMT z p R gs k).card := by
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
      have := img_mergeT z p R gs _ k hm
        (img_le_twoT z p R gs hgood _ k (runLT_inv z p R gs hT k) hm.1)
      omega
    · have hM : runMT z p R gs (k + 1) = runMT z p R gs k := by
        rw [runMT, ite_eq_right hm]
      rw [runLT_succ, hM, mstepT_nomerge z p R gs hm]
      exact ih

theorem run_sub_DT (k : ℕ) : runMT z p R gs k ⊆ DT z p R gs := by
  intro i hi
  obtain ⟨j, -, rfl, hm⟩ := (runMT_mem z p R gs k i).mp hi
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hm.2
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [trRT, Finset.mem_filter] at hu hv
  have hjl : j < gs.length := by
    by_contra hc
    have := hu.2
    rw [mr_val_ge gs _ _ (by omega)] at this
    exact absurd this (by simp)
  simp only [DT, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by omega, by omega⟩, hm.1, u, v, fun h => hxy (by rw [h]), hu.1, hv.1, hu.2, hv.2⟩

theorem run_indexT (k i : ℕ) (hi : i ∈ runMT z p R gs k) : ∃ j < k, i = n + j := by
  obtain ⟨j, hj, he, -⟩ := (runMT_mem z p R gs k i).mp hi
  exact ⟨j, hj, he⟩

theorem run_recordT (k j : ℕ) (hj : n + j ∈ runMT z p R gs k) :
    (∃ u ∈ R, ∃ v ∈ R, val gs (p u) (n + j) = true ∧ val gs (p v) (n + j) = true ∧
        runLT z p R gs j u ≠ runLT z p R gs j v) ∧
      ∀ u ∈ R, ∀ v ∈ R, val gs (p u) (n + j) = true → val gs (p v) (n + j) = true →
        runLT z p R gs (j + 1) u = runLT z p R gs (j + 1) v := by
  obtain ⟨j', -, he, hm⟩ := (runMT_mem z p R gs k _).mp hj
  obtain rfl : j' = j := by omega
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hm.2
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [trRT, Finset.mem_filter] at hu hv
    exact ⟨u, hu.1, v, hv.1, hu.2, hv.2, hxy⟩
  · intro u hu v hv hui hvi
    rw [runLT_succ, mstepT_merge z p R gs hm u (Finset.mem_filter.mpr ⟨hu, hui⟩),
      mstepT_merge z p R gs hm v (Finset.mem_filter.mpr ⟨hv, hvi⟩)]

theorem run_persistT (j k : ℕ) (u v : Fin n) (hjk : j ≤ k)
    (h : runLT z p R gs j u = runLT z p R gs j v) :
    runLT z p R gs k u = runLT z p R gs k v := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    obtain ⟨φ, hφ⟩ := mstepT_comp z p R gs (runLT z p R gs k) k
    rw [runLT_succ, hφ]
    show φ _ = φ _
    rw [ih]

/-- Strong form of "a pair of blocks is joined at most once". -/
theorem run_onceT (k j j' : ℕ) (u v : Fin n)
    (hj : runLT z p R gs (j + 1) u = runLT z p R gs (j + 1) v) (hjj : j < j')
    (htr : ∀ w ∈ R, val gs (p w) (n + j') = true → w = u ∨ w = v) :
    n + j' ∉ runMT z p R gs k := by
  intro hmem
  obtain ⟨j'', -, he, hm⟩ := (runMT_mem z p R gs k _).mp hmem
  obtain rfl : j'' = j' := by omega
  have hp := run_persistT z p R gs (j + 1) j'' u v (by omega) hj
  have key : ∀ w ∈ trRT p R gs (n + j''), runLT z p R gs j'' w = runLT z p R gs j'' u := by
    intro w hw
    rw [trRT, Finset.mem_filter] at hw
    rcases htr w hw.1 hw.2 with h | h
    · rw [h]
    · rw [h, hp]
  have hc : ((trRT p R gs (n + j'')).image (runLT z p R gs j'')).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [key a ha, key b hb]
  have := hm.2
  omega

theorem run_InvT (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u) :
    InvT z p R gs (runLT z p R gs gs.length) := by
  intro i u v hz hu hv huR hvR
  by_cases hi : i < n + gs.length
  · exact runLT_inv z p R gs hT gs.length i hi hz u huR v hvR hu hv
  · rw [mr_val_ge gs _ i (by omega)] at hu
    exact absurd hu (by simp)

/-- (T1) The explicit union-find run for general test systems, packaged. -/
theorem merge_runT (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (hgood : GoodT z p R gs) :
    ∃ (L : ℕ → Fin n → Fin n) (M : ℕ → Finset ℕ),
      L 0 = id ∧ M 0 = ∅ ∧
      (∀ k, ∀ i < n + k, val gs z i = false → ∀ u ∈ R, ∀ v ∈ R,
        val gs (p u) i = true → val gs (p v) i = true → L k u = L k v) ∧
      InvT z p R gs (L gs.length) ∧
      (∀ k, R.card ≤ (R.image (L k)).card + (M k).card) ∧
      (∀ k, M k ⊆ DT z p R gs) ∧ (∀ k, ∀ i ∈ M k, ∃ j < k, i = n + j) ∧
      (∀ k K, k ≤ K → M k ⊆ M K) ∧
      (∀ k j, n + j ∈ M k →
        (∃ u ∈ R, ∃ v ∈ R, val gs (p u) (n + j) = true ∧ val gs (p v) (n + j) = true ∧
          L j u ≠ L j v) ∧
        ∀ u ∈ R, ∀ v ∈ R, val gs (p u) (n + j) = true → val gs (p v) (n + j) = true →
          L (j + 1) u = L (j + 1) v) ∧
      (∀ j k u v, j ≤ k → L j u = L j v → L k u = L k v) ∧
      (∀ k j j' u v, u ∈ R → v ∈ R → L j u ≠ L j v → L (j + 1) u = L (j + 1) v → j < j' →
        (∀ w ∈ R, val gs (p w) (n + j') = true → w = u ∨ w = v) → n + j' ∉ M k) := by
  refine ⟨runLT z p R gs, runMT z p R gs, rfl, rfl, fun k => runLT_inv z p R gs hT k,
    run_InvT z p R gs hT, run_countT z p R gs hT hgood, run_sub_DT z p R gs,
    run_indexT z p R gs, runMT_mono z p R gs, run_recordT z p R gs, run_persistT z p R gs, ?_⟩
  intro k j j' u v _ _ _ hj hjj htr
  exact run_onceT z p R gs k j j' u v hj hjj htr

/-- (T1) Corollary, mirroring `countT_bound`. -/
theorem merge_countT (hT : ∀ u ∈ R, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (hgood : GoodT z p R gs) (o : ℕ) (hz : val gs z o = false)
    (hp : ∀ u ∈ R, val gs (p u) o = true) :
    R.card - 1 ≤ (runMT z p R gs gs.length).card := by
  have hc := run_countT z p R gs hT hgood gs.length
  have hinv := run_InvT z p R gs hT
  have h1 : (R.image (runLT z p R gs gs.length)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hb
    exact hinv o u v hz (hp u hu') (hp v hv') hu' hv'
  omega

end

end PEqualNP.Outside.L_meta_951_aux
