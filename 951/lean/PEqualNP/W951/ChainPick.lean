import PEqualNP.W951.Heavy
import Mathlib.Data.Fin.Tuple.Sort

/-! ChainPick: research's two-world chain lemma (CU, board agents/research-concave-dual.md) and what
actually gives the price form (coord assignment 09:24).

The left side of `MergePrice`, `π ↦ ∑ w, min_z π(M_z(w))`, is concave in `π`, so the inequality
for 0/1 prices does not give it for all `π` (the referee's point). Write `π` as a layer cake
`π = ∑ t c_t 1_{U_t}` over a chain of gate sets `U_0 ⊇ U_1 ⊇ ...` with `c_t ≥ 0` (`layerCake`).
Then `min_z π(M_z) ≥ ∑ t c_t min_z |M_z ∩ U_t|`: the layer cake bounds the left side from BELOW,
the wrong direction for an upper bound. A 0/1 statement gives the price form exactly when ONE pick
works on the whole chain.

* `ChainPick O` (abstract menus `O w` of gate sets): for every chain `U` there is ONE bundle
  `M w ∈ O w` per set with `∑ w |M w ∩ U t| ≤ |U t|` at every level `t`. `price_of_chainPick`:
  ChainPick gives the price inequality for every `π ≥ 0` (layer cake, right direction).
* `ChainWorld O` (research's CU): the menus split into two worlds; for every chain there is one
  WORLD choice per set, the bundle may still change from level to level. `WorldUniform O`: inside
  a world, for every chain one bundle is minimal at every level. `chainPick_of_chainWorld`:
  CU + WorldUniform gives ChainPick.
* `cu_counterexample`: CU ALONE DOES NOT give the price form. Two sets, four gates, menus
  `{0,3} | {1,2}` and `{2,3} | {1,3}` (one world): every chain passes (all 0/1 prices pass), but
  `π = (0, 1, 1, 2)` gives `2 + 3 > 4`. Set 0's best bundle is `{0,3}` on the level `{1,2,3}`
  and `{1,2}` on the level `{3}`: the within-world layer-cake gap research measured (≤ 1 per
  family on the data) is exactly what CU leaves open.
* Circuits: `ChainPickOn S gates A` (menus of merge sets over allowed points `A w`) gives
  `MergePriceOn` (`mergePriceOn_of_chainPickOn`), hence `MergePrice` (all zero points),
  `RefinedNoMixedPrice` (refined points) and `HeavySplitFloatPrice` (heavy float points), and
  `no_minCE_of_chainPick`. The circuit CU (`ChainWorldOn`, worlds `World0` / not `World0` of the
  allowed points) with `WorldUniformOn` gives `MergePriceOn` (`mergePriceOn_of_chainWorldOn`) and
  `no_minCE_of_chainWorld`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open Finset PEqualNP.CircuitLowerBounds

/-! ## Abstract menus: layer cake, ChainPick, CU -/

/-- Layer cake. -/
theorem layerCake {L : ℕ} (π : Fin L → ℝ) (hπ : ∀ a, 0 ≤ π a) :
    ∃ (U : ℕ → Finset (Fin L)) (c : ℕ → ℝ), Antitone U ∧ (∀ i, 0 ≤ c i) ∧
      ∀ T : Finset (Fin L), ∑ a ∈ T, π a = ∑ i ∈ range L, c i * ((T ∩ U i).card : ℝ) := by
  classical
  set σ := Tuple.sort π with hσ
  have hmono : Monotone (π ∘ σ) := Tuple.monotone_sort π
  let p : ℕ → ℝ := fun i => if h : i < L then π (σ ⟨i, h⟩) else 0
  let c : ℕ → ℝ := fun i => if i < L then p i - (if i = 0 then 0 else p (i - 1)) else 0
  let U : ℕ → Finset (Fin L) := fun i => univ.filter fun a => i ≤ ((σ.symm a : Fin L) : ℕ)
  have hp_le : ∀ i, i < L → 0 < i → p (i - 1) ≤ p i := by
    intro i hi h0
    simp only [p, dite_eq_left hi, dite_eq_left (show i - 1 < L by omega)]
    exact hmono (show (⟨i - 1, by omega⟩ : Fin L) ≤ ⟨i, hi⟩ from Fin.mk_le_mk.mpr (by omega))
  have htel : ∀ j, j < L → ∑ i ∈ range (j + 1), c i = p j := by
    intro j hj
    induction j with
    | zero =>
      simp [c, hj]
    | succ j ih =>
      rw [sum_range_succ, ih (by omega)]
      simp only [c, ite_eq_left hj, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel]
      ring
  have hpa : ∀ a : Fin L, π a = p (σ.symm a) := by
    intro a
    simp only [p, dite_eq_left (σ.symm a).isLt, Fin.eta, Equiv.apply_symm_apply]
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    simp only [c]
    split_ifs with hi h0
    · subst h0
      simp only [p, dite_eq_left hi, sub_zero]
      exact hπ _
    · linarith [hp_le i hi (by omega)]
    · exact le_rfl
  clear_value c p
  refine ⟨U, c, ?_, hc0, ?_⟩
  · intro i j hij a ha
    simp only [U, mem_filter, mem_univ, true_and] at ha ⊢
    omega
  · intro T
    calc ∑ a ∈ T, π a
        = ∑ a ∈ T, ∑ i ∈ range L, (if i ≤ ((σ.symm a : Fin L) : ℕ) then c i else 0) := by
          refine sum_congr rfl fun a _ => ?_
          have hk := (σ.symm a).isLt
          rw [hpa, ← htel _ hk, Finset.sum_ite, Finset.sum_const_zero, add_zero]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext i
          simp only [mem_filter, mem_range]
          constructor
          · intro h
            exact And.intro (by omega) (by omega)
          · intro h
            omega
      _ = ∑ i ∈ range L, c i * ((T ∩ U i).card : ℝ) := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          have hfi : T.filter (fun a => i ≤ ((σ.symm a : Fin L) : ℕ)) = T ∩ U i := by
            ext a
            simp [U]
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, hfi]

variable {ι : Type*} [Fintype ι] {L : ℕ}

def ChainPick (O : ι → Finset (Finset (Fin L))) : Prop :=
  ∀ U : ℕ → Finset (Fin L), Antitone U →
    ∃ M : ι → Finset (Fin L), (∀ w, M w ∈ O w) ∧ ∀ i, ∑ w, (M w ∩ U i).card ≤ (U i).card

theorem price_of_chainPick (O : ι → Finset (Finset (Fin L))) (hO : ∀ w, (O w).Nonempty)
    (h : ChainPick O) (π : Fin L → ℝ) (hπ : ∀ a, 0 ≤ π a) :
    ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a) ≤ ∑ a, π a := by
  obtain ⟨U, c, hU, hc, hlc⟩ := layerCake π hπ
  obtain ⟨M, hM, hcap⟩ := h U hU
  calc ∑ w, (O w).inf' (hO w) (fun M => ∑ a ∈ M, π a)
      ≤ ∑ w, ∑ a ∈ M w, π a := sum_le_sum fun w _ => inf'_le _ (hM w)
    _ = ∑ w, ∑ i ∈ range L, c i * ((M w ∩ U i).card : ℝ) := sum_congr rfl fun w _ => hlc (M w)
    _ = ∑ i ∈ range L, c i * ((∑ w, (M w ∩ U i).card : ℕ) : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        push_cast
        rw [mul_sum]
    _ ≤ ∑ i ∈ range L, c i * ((U i).card : ℝ) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hcap i) (hc i)
    _ = ∑ a, π a := by
        rw [hlc univ]
        simp

def ChainWorld (O : Bool → ι → Finset (Finset (Fin L))) : Prop :=
  ∀ U : ℕ → Finset (Fin L), Antitone U → ∃ b : ι → Bool, ∀ i,
    ∃ M : ι → Finset (Fin L), (∀ w, M w ∈ O (b w) w) ∧ ∑ w, (M w ∩ U i).card ≤ (U i).card

def WorldUniform (O : Bool → ι → Finset (Finset (Fin L))) : Prop :=
  ∀ U : ℕ → Finset (Fin L), Antitone U → ∀ (w : ι) (b : Bool), (O b w).Nonempty →
    ∃ M ∈ O b w, ∀ i, ∀ M' ∈ O b w, (M ∩ U i).card ≤ (M' ∩ U i).card

theorem chainPick_of_chainWorld (O : Bool → ι → Finset (Finset (Fin L)))
    (hCU : ChainWorld O) (hWU : WorldUniform O) : ChainPick (fun w => O false w ∪ O true w) := by
  intro U hU
  obtain ⟨b, hb⟩ := hCU U hU
  have hne : ∀ w, (O (b w) w).Nonempty := fun w => by
    obtain ⟨M, hM, -⟩ := hb 0
    exact ⟨M w, hM w⟩
  choose M hM hunif using fun w => hWU U hU w (b w) (hne w)
  refine ⟨M, fun w => ?_, fun i => ?_⟩
  · have := hM w
    cases hbw : b w <;> rw [hbw] at this <;> simp [this]
  · obtain ⟨M', hM', hle⟩ := hb i
    exact (sum_le_sum fun w _ => hunif w i (M' w) (hM' w)).trans hle

/-- The menus of the counterexample (all in world `false`). -/
def cuMenu : Fin 2 → Finset (Finset (Fin 4)) := ![{{0, 3}, {1, 2}}, {{2, 3}, {1, 3}}]

def cuO : Bool → Fin 2 → Finset (Finset (Fin 4)) := fun b w => if b then ∅ else cuMenu w

theorem cuMenu_nonempty (w : Fin 2) : (cuMenu w).Nonempty := by
  fin_cases w <;> simp [cuMenu]

def cuPick (A : Finset (Fin 4)) : Fin 2 → Finset (Fin 4) :=
  ![if (({0, 3} : Finset (Fin 4)) ∩ A).card ≤ (({1, 2} : Finset (Fin 4)) ∩ A).card then {0, 3} else {1, 2},
    if (({2, 3} : Finset (Fin 4)) ∩ A).card ≤ (({1, 3} : Finset (Fin 4)) ∩ A).card then {2, 3} else {1, 3}]

theorem cuPick_spec : ∀ A : Finset (Fin 4),
    (∀ w, cuPick A w ∈ cuMenu w) ∧ ∑ w, (cuPick A w ∩ A).card ≤ A.card := by
  decide

theorem cu_counterexample :
    ChainWorld cuO ∧
      ∃ π : Fin 4 → ℝ, (∀ a, 0 ≤ π a) ∧
        ∑ a, π a < ∑ w, (cuMenu w).inf' (cuMenu_nonempty w) (fun M => ∑ a ∈ M, π a) := by
  refine ⟨fun U _ => ⟨fun _ => false, fun i => ⟨cuPick (U i), fun w => ?_, (cuPick_spec (U i)).2⟩⟩, ?_⟩
  · simpa [cuO] using (cuPick_spec (U i)).1 w
  · refine ⟨![0, 1, 1, 2], fun a => by fin_cases a <;> simp, ?_⟩
    have h0 : (2 : ℝ) ≤ (cuMenu 0).inf' (cuMenu_nonempty 0) (fun M => ∑ a ∈ M, (![0, 1, 1, 2] : Fin 4 → ℝ) a) := by
      apply le_inf'
      intro M hM
      simp only [cuMenu, Matrix.cons_val_zero, mem_insert, mem_singleton] at hM
      rcases hM with rfl | rfl <;> norm_num
    have h1 : (3 : ℝ) ≤ (cuMenu 1).inf' (cuMenu_nonempty 1) (fun M => ∑ a ∈ M, (![0, 1, 1, 2] : Fin 4 → ℝ) a) := by
      apply le_inf'
      intro M hM
      simp [cuMenu] at hM
      rcases hM with rfl | rfl <;> simp <;> norm_num
    have hsum : ∑ a, (![0, 1, 1, 2] : Fin 4 → ℝ) a = 4 := by
      simp [Fin.sum_univ_four]; norm_num
    rw [hsum, Fin.sum_univ_two]
    linarith


/-! ## Circuits: menus of merge sets -/

section Circuits

variable {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)

/-- The menu of set `w` over the allowed points `A w`: the gate indices of its merge sets. -/
noncomputable def mergeMenu (A : Fin m → Finset (Fin n → Bool)) (w : Fin m) :
    Finset (Finset (Fin gates.length)) :=
  (A w).image (mergeIdx gates (S w))

/-- **ChainPick on allowed points**: for every chain of gate sets there is ONE allowed point per set
whose merge set meets every level `U t` in at most `|U t|` gates in total. -/
def ChainPickOn (A : Fin m → Finset (Fin n → Bool)) : Prop :=
  ChainPick (mergeMenu S gates A)

/-- **ChainPick gives the price form on the same allowed points.** -/
theorem mergePriceOn_of_chainPickOn (A : Fin m → Finset (Fin n → Bool))
    (hA : ∀ w, (A w).Nonempty) (h : ChainPickOn S gates A) : MergePriceOn S gates A hA := by
  intro π hπ
  have hO : ∀ w, (mergeMenu S gates A w).Nonempty := fun w => (hA w).image _
  have key := price_of_chainPick (mergeMenu S gates A) hO h (fun a => π (n + (a : ℕ)))
    (fun a => hπ _)
  rw [sum_Ico_eq_sum_fin]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun w _ => ?_) key
  simp only [mergeMenu]
  rw [Finset.inf'_image]
  refine Finset.inf'_congr _ rfl fun z _ => ?_
  simp only [Function.comp_apply, sum_mergeSet]

/-- ChainPick on all zero points gives `MergePrice`. -/
theorem mergePrice_of_chainPick (h : ChainPickOn S gates (fun w => zeroPts (S w))) :
    MergePrice S gates :=
  (mergePriceOn_zeroPts_iff S gates).mp
    (mergePriceOn_of_chainPickOn S gates _ (fun _ => zeroPts_nonempty _) h)

/-- ChainPick on the refined points gives the refined price form (Case I). -/
theorem refinedNoMixedPrice_of_chainPick (p : ℕ) (hA : ∀ w, (refinedPts S gates p w).Nonempty)
    (h : ChainPickOn S gates (refinedPts S gates p)) : RefinedNoMixedPrice S gates p hA :=
  mergePriceOn_of_chainPickOn S gates _ hA h

/-- ChainPick on the heavy float points gives the price form of Case II. -/
theorem heavySplitFloatPrice_of_chainPick (v : Fin n)
    (h : ChainPickOn S gates (heavyFloatPts S v)) : HeavySplitFloatPrice S gates v :=
  mergePriceOn_of_chainPickOn S gates _ (heavyFloatPts_nonempty S v) h

open Classical in
/-- The two worlds of the allowed points (research's split): world `false` = `World0` (`h z = 1`),
world `true` = the other allowed points. -/
noncomputable def worldMenuOn (A : Fin m → Finset (Fin n → Bool)) (b : Bool) (w : Fin m) :
    Finset (Finset (Fin gates.length)) :=
  ((A w).filter fun z => (World0 gates z ↔ b = false)).image (mergeIdx gates (S w))

/-- **Research's CU on allowed points**: for every chain, one world per set such that every level
passes its 0/1 check with bundles from those worlds (the bundle may change with the level). -/
def ChainWorldOn (A : Fin m → Finset (Fin n → Bool)) : Prop :=
  ChainWorld (worldMenuOn S gates A)

/-- Within each world one bundle is minimal at every level of every chain. -/
def WorldUniformOn (A : Fin m → Finset (Fin n → Bool)) : Prop :=
  WorldUniform (worldMenuOn S gates A)

theorem worldMenuOn_union (A : Fin m → Finset (Fin n → Bool)) (w : Fin m) :
    worldMenuOn S gates A false w ∪ worldMenuOn S gates A true w = mergeMenu S gates A w := by
  classical
  simp only [worldMenuOn, mergeMenu, ← Finset.image_union]
  congr 1
  ext z
  simp only [mem_union, mem_filter]
  tauto

/-- **CU + within-world uniformity gives the price form** (on any allowed points). -/
theorem mergePriceOn_of_chainWorldOn (A : Fin m → Finset (Fin n → Bool))
    (hA : ∀ w, (A w).Nonempty) (hCU : ChainWorldOn S gates A) (hWU : WorldUniformOn S gates A) :
    MergePriceOn S gates A hA := by
  apply mergePriceOn_of_chainPickOn S gates A hA
  have h := chainPick_of_chainWorld _ hCU hWU
  unfold ChainPickOn
  simpa only [worldMenuOn_union] using h

end Circuits

/-- **ChainPick on minimal counterexamples closes 951.** -/
theorem no_minCE_of_chainPick
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ChainPickOn S gates (fun w => zeroPts (S w))) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergePrice fun n m S gates out M => mergePrice_of_chainPick S gates (H n m S gates out M)

/-- **CU + within-world uniformity on minimal counterexamples closes 951.** -/
theorem no_minCE_of_chainWorld
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ChainWorldOn S gates (fun w => zeroPts (S w)) ∧
        WorldUniformOn S gates (fun w => zeroPts (S w))) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out :=
  no_minCE_of_mergePrice fun n m S gates out M => by
    obtain ⟨hCU, hWU⟩ := H n m S gates out M
    exact (mergePriceOn_zeroPts_iff S gates).mp
      (mergePriceOn_of_chainWorldOn S gates _ (fun _ => zeroPts_nonempty _) hCU hWU)

end PEqualNP.Outside.L_meta_951_aux
