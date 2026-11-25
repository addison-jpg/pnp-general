import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.NotVarF2

/-!
# CubeF2: the relative form of front A2's case `h = x_a` (local closure of the F2 induction)

Front A2 (12:55), relative form over the cube `x_Q = 1` (referee dwV8p: plain and relative form
correct). If on the cube the NOT gate computes `¬x_a` (`a ∉ Q`) or a constant, then
`base(Q) ≤ |F2(Q)|` directly: the alive sets at `Q` have a lifted SDR whose gates are real F2 gates
with `Q` fixed to `1`.

* The generic cube test system `cubeLTS Q T y0 yat`: zero point `(Zof T, y0)`, atoms
  `(Q + e_u, yat u)`. `CubeOK` lists the conditions for one set `R` (the zero point and the atoms are
  the `ν`-lifts of real points of the cube, `R ⊆ T`, `T` misses `Q`, and `yat u` lies below `y0` and
  below `ν(Zof T + e_u)`). `cubeLTS_valid`, `cubeLTS_disjoint` (from `CubePair`: of two points of `R`
  one has its atom below the other zero point), `lowerWire_mem_F2_cube` (real witness
  `(Zof T, u, u')`, `1` on `Q`).
* **`baseDQ_le_F2_of_cube`**: such systems for all alive sets, pairwise `CubePair` in one direction
  ⇒ `base(Q) ≤ |F2(Q)|`.
* Instances: `cubeOK_var` (`h = x_a` on the cube, `T = R ∪ {a}`, `y0 = 1`, `yat u = [u ≠ a]`;
  pairs by `xv_pairs`), `cubeOK_const` (`ν = b` on the cube, `T = R`, `y0 = yat = b`; pairs by
  `|R ∩ R'| ≤ 1`). `CubeLocal gates p Q` (either case), **`baseDQ_le_F2_of_cubeLocal`**.
* Front's LW1 (relative form, 13:19): `LW1 gates p S Q` (zero points `z_w ⊇ Q` off `S_w` with
  `h(z_w) = 0`, light points stay light at `z_w + e_u`, pairwise `|S_w' \ z_w| ≤ 1` or
  `|S_w \ z_w'| ≤ 1`), `cubeOK_LW1` (`T = {z_w = 0}`, `y0 = 1`, `yat u = ν(Q + e_u)`),
  **`baseDQ_le_F2_of_LW1`**. The NotVar classes are the case `z_w = top_w \ {a}`.
* The induction with local closures: `base_le_F2_pts_or` (at every `Q` with positive base, either
  `base(Q) ≤ |F2(Q)|` or a `GainF2` step), **`no_minCE_of_gainF2_or_cubeLocal`** and
  **`no_minCE_of_gainF2_or_local`** (every `Q` with positive base is `CubeLocal`, satisfies LW1, or has
  a `GainF2` step ⇒ no minimal counterexample).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CubeF2

variable {n m : ℕ}

/-- The cube atom of `u`: `(Q + e_u, yat u)`. -/
def cubeAtom (Q : Finset (Fin n)) (yat : Fin n → Bool) (c : Fin (n + 1)) : Fin (n + 1) → Bool :=
  if h : c = Fin.last n then canonPt ∅
  else ext (canonPt (insert (c.castPred h) Q)) (yat (c.castPred h))

theorem cubeAtom_castSucc (Q : Finset (Fin n)) (yat : Fin n → Bool) (u : Fin n) :
    cubeAtom Q yat (Fin.castSucc u) = ext (canonPt (insert u Q)) (yat u) := by
  rw [cubeAtom, dite_eq_right (Fin.castSucc_ne_last u), Fin.castPred_castSucc]

/-- **The cube test system**: zero point `(Zof T, y0)`, atoms `(Q + e_u, yat u)`. -/
def cubeLTS (Q T : Finset (Fin n)) (y0 : Bool) (yat : Fin n → Bool) : LTS n :=
  ⟨ext (Zof T) y0, cubeAtom Q yat⟩

theorem Zof_of_disjoint {Q T : Finset (Fin n)} (h : Disjoint Q T) {x : Fin n} (hx : x ∈ Q) :
    Zof T x = true := by
  simp [Zof, Finset.disjoint_left.mp h hx]

/-- **The conditions on one set `R`** (NOT gate at `p`, cube `x_Q = 1`). -/
structure CubeOK (gates : List Gate) (p : ℕ) (Q R T : Finset (Fin n)) (y0 : Bool)
    (yat : Fin n → Bool) : Prop where
  hQT : Disjoint Q T
  hRT : R ⊆ T
  hz : val gates (Zof T) (n + p) = y0
  hat : ∀ u ∈ R, val gates (canonPt (insert u Q)) (n + p) = yat u
  hy : ∀ u ∈ R, yat u ≤ y0
  hF : ∀ u ∈ R, yat u ≤ val gates (Function.update (Zof T) u true) (n + p)

/-- **The pair condition**: of two distinct points of `R`, one has its atom below the zero point
`(Zof T', y0')`. -/
def CubePair (R T' : Finset (Fin n)) (y0' : Bool) (yat : Fin n → Bool) : Prop :=
  ∀ u ∈ R, ∀ v ∈ R, u ≠ v → (u ∉ T' ∧ yat u ≤ y0') ∨ (v ∉ T' ∧ yat v ≤ y0')

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

/-- The atom of `u ∈ R` is `1` off the zero point only at `u`. -/
theorem cube_sep {Q R T : Finset (Fin n)} {y0 : Bool} {yat : Fin n → Bool}
    (hk : CubeOK gates p Q R T y0 yat) {u : Fin n} (hu : u ∈ R) (x : Fin (n + 1))
    (h1 : cubeAtom Q yat (Fin.castSucc u) x = true) (h0 : ext (Zof T) y0 x = false) :
    x = Fin.castSucc u := by
  rw [cubeAtom_castSucc] at h1
  induction x using Fin.lastCases with
  | last =>
    rw [ext_last] at h1 h0
    have := hk.hy u hu
    rw [h1, h0] at this
    exact absurd this (by decide)
  | cast y =>
    rw [ext_castSucc] at h1 h0
    rcases Finset.mem_insert.mp (canonPt_eq_true.mp h1) with rfl | hyQ
    · rfl
    · rw [Zof_of_disjoint hk.hQT hyQ] at h0
      exact absurd h0 (by decide)

include hp in
/-- **Validity** of the cube test system (correct output). -/
theorem cubeLTS_valid {Q R T : Finset (Fin n)} {y0 : Bool} {yat : Fin n → Bool} (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true))
    (hk : CubeOK gates p Q R T y0 yat) : LTSValid gates p R o (cubeLTS Q T y0 yat) := by
  refine ⟨?_, fun c hc => ?_, fun x hx c hc c' hc' h1 h2 => ?_⟩
  · show val (lift n p gates) (ext (Zof T) y0) (liftWire n p o) = false
    have key := val_lift (n := n) gates p hp (Zof T) o
    rw [hk.hz, hev] at key
    rw [← key]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    have : Zof T v = false := by simp [Zof, hk.hRT hv]
    rw [this] at hzv
    exact absurd hzv (by decide)
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    show val (lift n p gates) (cubeAtom Q yat (Fin.castSucc u)) (liftWire n p o) = true
    rw [cubeAtom_castSucc]
    have key := val_lift (n := n) gates p hp (canonPt (insert u Q)) o
    rw [hk.hat u hu, hev] at key
    rw [← key]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_insert_self u Q)⟩
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp hc'
    rw [← cube_sep gates p hk hu x h1 hx, ← cube_sep gates p hk hv x h2 hx]

/-- The atom of a point outside `T'` (with `yat u ≤ y0'`) lies below the zero point `(Zof T', y0')`. -/
theorem cubeAtom_le_zero {Q T' : Finset (Fin n)} {yat : Fin n → Bool} {y0' : Bool} {u : Fin n}
    (hQT' : Disjoint Q T') (hu : u ∉ T') (hy : yat u ≤ y0') :
    cubeAtom Q yat (Fin.castSucc u) ≤ ext (Zof T') y0' := by
  rw [cubeAtom_castSucc]
  refine ext_le_of_le (canonPt_le fun x hx => ?_) hy
  rcases Finset.mem_insert.mp hx with rfl | hxQ
  · simp [Zof, hu]
  · exact Zof_of_disjoint hQT' hxQ

include hp hg hU hN in
/-- **Disjointness** (lifted Theorem U, one direction) from the pair condition. -/
theorem cubeLTS_disjoint (Q R R' T T' : Finset (Fin n)) (y0 y0' : Bool) (yat yat' : Fin n → Bool)
    (hQT' : Disjoint Q T') (h : CubePair R T' y0' yat) :
    Disjoint (ltsCls gates p R (cubeLTS Q T y0 yat)) (ltsCls gates p R' (cubeLTS Q T' y0' yat')) := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  rcases h u hu v hv huv with h1 | h1
  · exact Or.inl (cubeAtom_le_zero hQT' h1.1 h1.2)
  · exact Or.inr (cubeAtom_le_zero hQT' h1.1 h1.2)

include hp hg hU hN in
/-- **The cube classes lie in F2(Q)**: the real wire of a gate of the class of an alive set `S_w` is
an OR gate with the real witness `(Zof T, u, u')`, `1` on `Q`. -/
theorem lowerWire_mem_F2_cube (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (w : Fin m)
    (hw : w ∈ aliveSets S Q) {T : Finset (Fin n)} {y0 : Bool} {yat : Fin n → Bool}
    (hk : CubeOK gates p Q (S w) T y0 yat) {i : ℕ}
    (hi : i ∈ ltsCls gates p (S w) (cubeLTS Q T y0 yat)) : lowerWire n p i ∈ F2 gates S Q := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  obtain ⟨j, rfl, hor⟩ := runMT_or _ _ _ _ hm (fun c hc c' h1 h0 => by
    obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    exact cube_sep gates p hk hu c' h1 h0) hi
  have h1 := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter, Finset.mem_Ico] at h1
  obtain ⟨⟨-, hjl⟩, hz, c, c', hcc, hc, hc', h1c, h1c'⟩ := h1
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨u', hu', rfl⟩ := mem_liftSet_iff.mp hc'
  have hjl' : j < (lift n p gates).length := by omega
  obtain ⟨k, hk', hork⟩ := lowerWire_isOr gates p hp hjl' hor
  have hge : n + 1 ≤ n + 1 + j := by omega
  have hatom : ∀ t ∈ S w,
      cubeAtom Q yat (Fin.castSucc t) ≤ nuPt gates p (Function.update (Zof T) t true) := by
    intro t ht
    rw [cubeAtom_castSucc, nuPt]
    refine ext_le_of_le (canonPt_le fun x hx => ?_) (hk.hF t ht)
    by_cases hxt : x = t
    · subst hxt
      simp
    · rw [Function.update_of_ne hxt]
      exact Zof_of_disjoint hk.hQT ((Finset.mem_insert.mp hx).resolve_left hxt)
  refine mem_F2.mpr ⟨⟨k, hk', hork⟩, w, hw, Zof T, u, u', hu, hu', fun h => hcc (h ▸ rfl),
    fun x hx => by simp [Zof, hk.hRT hx], fun x hx => Zof_of_disjoint hk.hQT hx, ?_, ?_, ?_⟩
  · exact real_zero_of_lift gates p hp hg hU hN hge (ζ := ext (Zof T) y0)
      (le_of_eq (by rw [nuPt, hk.hz])) hz
  · exact real_one_of_lift gates p hp hg hU hN hge (hatom u hu) h1c
  · exact real_one_of_lift gates p hp hg hU hN hge (hatom u' hu') h1c'

include hp hg hU hN in
/-- **The cube SDR ⇒ `base(Q) ≤ |F2(Q)|`.** -/
theorem baseDQ_le_F2_of_cube (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (T : Fin m → Finset (Fin n)) (y0 : Fin m → Bool) (yat : Fin m → Fin n → Bool)
    (hk : ∀ w ∈ aliveSets S Q, CubeOK gates p Q (S w) (T w) (y0 w) (yat w))
    (hpair : ∀ w ∈ aliveSets S Q, ∀ w' ∈ aliveSets S Q, w ≠ w' →
      CubePair (S w) (T w') (y0 w') (yat w) ∨ CubePair (S w') (T w) (y0 w) (yat w')) :
    baseDQ S ∅ Q ≤ (F2 gates S Q).card := by
  classical
  set C : Fin m → Finset ℕ := fun w => ltsCls gates p (S w) (cubeLTS Q (T w) (y0 w) (yat w))
    with hC
  have hpd : ((aliveSets S Q : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint C := by
    intro w hw w' hw' hww
    rcases hpair w hw w' hw' hww with h | h
    · exact cubeLTS_disjoint gates p hp hg hU hN Q (S w) (S w') (T w) (T w') (y0 w) (y0 w')
        (yat w) (yat w') (hk w' hw').hQT h
    · exact (cubeLTS_disjoint gates p hp hg hU hN Q (S w') (S w) (T w') (T w) (y0 w') (y0 w)
        (yat w') (yat w) (hk w hw).hQT h).symm
  have hinj : Set.InjOn (lowerWire n p) ↑((aliveSets S Q).biUnion C) := by
    intro i hi i' hi' h
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hi)
    obtain ⟨w', -, hw'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hi')
    have r := Finset.mem_Ico.mp (ltsCls_subset gates p (S w) _ hw)
    have r' := Finset.mem_Ico.mp (ltsCls_subset gates p (S w') _ hw')
    exact lowerWire_injOn r.1 r'.1 h
  have hb : baseDQ S ∅ Q = ∑ w ∈ aliveSets S Q, ((S w).card - 1) := by
    simp [baseDQ]
  rw [hb]
  calc ∑ w ∈ aliveSets S Q, ((S w).card - 1)
      ≤ ∑ w ∈ aliveSets S Q, (C w).card := Finset.sum_le_sum fun w hw =>
        card_ltsCls gates p hp hg hU hN (S w) (out w) _
          (cubeLTS_valid gates p hp (out w) (hev w) (hk w hw))
    _ = ((aliveSets S Q).biUnion C).card := (Finset.card_biUnion hpd).symm
    _ = (((aliveSets S Q).biUnion C).image (lowerWire n p)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (F2 gates S Q).card := Finset.card_le_card fun g hg' => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg'
        obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
        exact lowerWire_mem_F2_cube gates p hp hg hU hN S Q w hw (hk w hw) hiw

/-! ## The two instances: `h = x_a` and `h` constant on the cube -/

/-- **The literal cube**: on the cube `x_Q = 1` the NOT gate computes `¬x_a` (`a ∉ Q`). -/
theorem cubeOK_var (Q R : Finset (Fin n)) (hRQ : Disjoint R Q) (a : Fin n) (haQ : a ∉ Q)
    (hh : ∀ x : Fin n → Bool, (∀ q ∈ Q, x q = true) → val gates x (n + p) = !x a) :
    CubeOK gates p Q R (insert a R) true (fun u => decide (u ≠ a)) := by
  have hQT : Disjoint Q (insert a R) := Finset.disjoint_insert_right.mpr ⟨haQ, hRQ.symm⟩
  refine ⟨hQT, Finset.subset_insert a R, ?_, fun u _ => ?_, fun u _ => Bool.le_true _,
    fun u _ => ?_⟩
  · rw [hh _ fun q hq => Zof_of_disjoint hQT hq, Zof_insert_self]
    rfl
  · rw [hh _ fun q hq => canonPt_eq_true.mpr (Finset.mem_insert_of_mem hq)]
    by_cases hua : u = a
    · subst hua
      simp [canonPt]
    · simp [canonPt, haQ, Ne.symm hua, hua]
  · have hcube : ∀ q ∈ Q, Function.update (Zof (insert a R)) u true q = true := by
      intro q hq
      by_cases hqu : q = u
      · subst hqu
        simp
      · rw [Function.update_of_ne hqu]
        exact Zof_of_disjoint hQT hq
    rw [hh _ hcube]
    by_cases hua : u = a
    · subst hua
      simp
    · rw [Function.update_of_ne (Ne.symm hua), Zof_insert_self]
      exact Bool.le_true _

/-- **The constant cube**: on the cube `x_Q = 1` the NOT gate is constant `b`. -/
theorem cubeOK_const (Q R : Finset (Fin n)) (hRQ : Disjoint R Q) (b : Bool)
    (hc : ∀ x : Fin n → Bool, (∀ q ∈ Q, x q = true) → val gates x (n + p) = b) :
    CubeOK gates p Q R R b (fun _ => b) := by
  refine ⟨hRQ.symm, le_rfl, hc _ fun q hq => Zof_of_disjoint hRQ.symm hq,
    fun u _ => hc _ fun q hq => canonPt_eq_true.mpr (Finset.mem_insert_of_mem hq),
    fun _ _ => le_rfl, fun u _ => le_of_eq (hc _ fun q hq => ?_).symm⟩
  by_cases hqu : q = u
  · subst hqu
    simp
  · rw [Function.update_of_ne hqu]
    exact Zof_of_disjoint hRQ.symm hq

theorem cubePair_var (a : Fin n) {R R' : Finset (Fin n)} (hRR : (R ∩ R').card ≤ 1) :
    CubePair R (insert a R') true (fun u => decide (u ≠ a)) ∨
      CubePair R' (insert a R) true (fun u => decide (u ≠ a)) := by
  rcases xv_pairs a hRR with h | h
  · left
    intro u hu v hv huv
    rcases h u hu v hv huv with h1 | h1
    · exact Or.inl ⟨h1, Bool.le_true _⟩
    · exact Or.inr ⟨h1, Bool.le_true _⟩
  · right
    intro u hu v hv huv
    rcases h u hu v hv huv with h1 | h1
    · exact Or.inl ⟨h1, Bool.le_true _⟩
    · exact Or.inr ⟨h1, Bool.le_true _⟩

theorem cubePair_const (b : Bool) {R R' : Finset (Fin n)} (hRR : (R ∩ R').card ≤ 1) :
    CubePair R R' b (fun _ => b) := by
  intro u hu v hv huv
  by_cases hu' : u ∈ R'
  · by_cases hv' : v ∈ R'
    · have : 1 < (R ∩ R').card := Finset.one_lt_card.mpr
        ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩, v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
      omega
    · exact Or.inr ⟨hv', le_rfl⟩
  · exact Or.inl ⟨hu', le_rfl⟩

/-- **The local cases**: on the cube `x_Q = 1` the NOT gate computes an input literal `¬x_a` with
`a ∉ Q`, or a constant. -/
def CubeLocal (gates : List Gate) (p : ℕ) (Q : Finset (Fin n)) : Prop :=
  (∃ a, a ∉ Q ∧ ∀ x : Fin n → Bool, (∀ q ∈ Q, x q = true) → val gates x (n + p) = !x a) ∨
    ∃ b, ∀ x : Fin n → Bool, (∀ q ∈ Q, x q = true) → val gates x (n + p) = b

include hp hg hU hN in
/-- **Local closure**: if the NOT gate is an input literal or constant on the cube `x_Q = 1`, then
`base(Q) ≤ |F2(Q)|`. No minimality. -/
theorem baseDQ_le_F2_of_cubeLocal (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (Q : Finset (Fin n)) (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hL : CubeLocal gates p Q) : baseDQ S ∅ Q ≤ (F2 gates S Q).card := by
  rcases hL with ⟨a, haQ, hh⟩ | ⟨b, hc⟩
  · exact baseDQ_le_F2_of_cube gates p hp hg hU hN S out Q hev (fun w => insert a (S w))
      (fun _ => true) (fun _ u => decide (u ≠ a))
      (fun w hw => cubeOK_var gates p Q (S w) (mem_aliveSets.mp hw) a haQ hh)
      (fun w _ w' _ hww => cubePair_var a (hS w w' hww))
  · exact baseDQ_le_F2_of_cube gates p hp hg hU hN S out Q hev S (fun _ => b) (fun _ _ => b)
      (fun w hw => cubeOK_const gates p Q (S w) (mem_aliveSets.mp hw) b hc)
      (fun w _ w' _ hww => Or.inl (cubePair_const b (hS w w' hww)))

/-! ## Front's LW1 (relative form): a third local closure -/

/-- **LW1 at `Q`** (front A2, 13:19): zero points `z_w ⊇ Q` vanishing on `S_w` with `h(z_w) = 0` (the
NOT gate is `1`), light points (NOT gate `1` at `Q + e_u`) staying light at `z_w + e_u`, and for every
pair of alive sets `|S_w' \ z_w| ≤ 1` or `|S_w \ z_w'| ≤ 1`. -/
def LW1 (gates : List Gate) (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Prop :=
  ∃ z : Fin m → Fin n → Bool,
    (∀ w ∈ aliveSets S Q, (∀ q ∈ Q, z w q = true) ∧ (∀ u ∈ S w, z w u = false) ∧
      val gates (z w) (n + p) = true ∧
      ∀ u ∈ S w, val gates (canonPt (insert u Q)) (n + p) = true →
        val gates (Function.update (z w) u true) (n + p) = true) ∧
    ∀ w ∈ aliveSets S Q, ∀ w' ∈ aliveSets S Q, w ≠ w' →
      ((S w').filter fun u => z w u = false).card ≤ 1 ∨
        ((S w).filter fun u => z w' u = false).card ≤ 1

theorem Zof_filter_false (z : Fin n → Bool) :
    Zof (Finset.univ.filter fun x => z x = false) = z := by
  funext x
  cases h : z x <;> simp [Zof, h]

/-- An LW1 zero point gives a cube test system: `T = {z = 0}`, `y0 = 1`, `yat u = ν(Q + e_u)`. -/
theorem cubeOK_LW1 (Q R : Finset (Fin n)) (z : Fin n → Bool) (hzQ : ∀ q ∈ Q, z q = true)
    (hzR : ∀ u ∈ R, z u = false) (hz : val gates z (n + p) = true)
    (hlight : ∀ u ∈ R, val gates (canonPt (insert u Q)) (n + p) = true →
      val gates (Function.update z u true) (n + p) = true) :
    CubeOK gates p Q R (Finset.univ.filter fun x => z x = false) true
      (fun u => val gates (canonPt (insert u Q)) (n + p)) := by
  refine ⟨Finset.disjoint_left.mpr fun q hq hqT => ?_, fun u hu => ?_, ?_, fun _ _ => rfl,
    fun _ _ => Bool.le_true _, fun u hu => ?_⟩
  · rw [Finset.mem_filter, hzQ q hq] at hqT
    exact absurd hqT.2 (by decide)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hzR u hu⟩
  · rw [Zof_filter_false]
    exact hz
  · rw [Zof_filter_false]
    cases hl : val gates (canonPt (insert u Q)) (n + p)
    · exact Bool.false_le _
    · rw [hlight u hu hl]

theorem cubePair_of_card {R : Finset (Fin n)} {z : Fin n → Bool} (yat : Fin n → Bool)
    (h : (R.filter fun u => z u = false).card ≤ 1) :
    CubePair R (Finset.univ.filter fun x => z x = false) true yat := by
  intro u hu v hv huv
  by_cases hu' : z u = false
  · by_cases hv' : z v = false
    · have : 1 < (R.filter fun u => z u = false).card := Finset.one_lt_card.mpr
        ⟨u, Finset.mem_filter.mpr ⟨hu, hu'⟩, v, Finset.mem_filter.mpr ⟨hv, hv'⟩, huv⟩
      omega
    · exact Or.inr ⟨fun h => hv' (Finset.mem_filter.mp h).2, Bool.le_true _⟩
  · exact Or.inl ⟨fun h => hu' (Finset.mem_filter.mp h).2, Bool.le_true _⟩

include hp hg hU hN in
/-- **LW1 ⇒ `base(Q) ≤ |F2(Q)|`** (front A2's LW1 in relative form; no minimality). -/
theorem baseDQ_le_F2_of_LW1 (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Q : Finset (Fin n))
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (hL : LW1 gates p S Q) : baseDQ S ∅ Q ≤ (F2 gates S Q).card := by
  obtain ⟨z, hz, hpair⟩ := hL
  refine baseDQ_le_F2_of_cube gates p hp hg hU hN S out Q hev
    (fun w => Finset.univ.filter fun x => z w x = false) (fun _ => true)
    (fun _ u => val gates (canonPt (insert u Q)) (n + p))
    (fun w hw => cubeOK_LW1 gates p Q (S w) (z w) (hz w hw).1 (hz w hw).2.1 (hz w hw).2.2.1
      (hz w hw).2.2.2) (fun w hw w' hw' hww => ?_)
  rcases hpair w hw w' hw' hww with h | h
  · exact Or.inr (cubePair_of_card _ h)
  · exact Or.inl (cubePair_of_card _ h)

/-! ## The F2 induction with local closures -/

/-- **The F2 induction with local closures**: at every `Q` with positive base, either
`base(Q) ≤ |F2(Q)|` holds directly or some `v ∉ Q` has the F2 step ⇒ `base(Q) ≤ |F2(Q)|`. -/
theorem base_le_F2_pts_or (S : Fin m → Finset (Fin n))
    (H : ∀ Q, 0 < baseDQ S ∅ Q →
      baseDQ S ∅ Q ≤ (F2 gates S Q).card ∨ ∃ v, v ∉ Q ∧ GainF2 gates S Q v) :
    ∀ k (Q : Finset (Fin n)), (Finset.univ \ Q).card ≤ k →
      baseDQ S ∅ Q ≤ (F2 gates S Q).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    rcases H Q hpos with hloc | ⟨v, hvQ, -⟩
    · exact hloc
    have : v ∈ Finset.univ \ Q := by simp [hvQ]
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hk)] at this
    exact absurd this (Finset.notMem_empty v)
  | succ k ih =>
    intro Q hk
    rcases Nat.eq_zero_or_pos (baseDQ S ∅ Q) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    rcases H Q hpos with hloc | ⟨v, hvQ, hgain⟩
    · exact hloc
    have hv : v ∈ Finset.univ \ Q := by simp [hvQ]
    have hih := ih (insert v Q) (by rw [Finset.sdiff_insert, Finset.card_erase_of_mem hv]; omega)
    have hb := baseDQ_insertQ S ∅ Q v
    have hcard := Finset.card_sdiff_add_card_eq_card (F2_insert_subset gates S Q v)
    have hstar : ∑ w ∈ starSets S Q v, ((S w \ ∅).card - 1) =
        ∑ w ∈ starSets S Q v, ((S w).card - 1) := by simp
    unfold GainF2 at hgain
    omega

end CubeF2

/-- **951 from the F2 step with local closures**: if every minimal counterexample has a NOT gate
such that every `Q` with positive base is `CubeLocal` (the NOT gate is an input literal `¬x_a`,
`a ∉ Q`, or constant on the cube `x_Q = 1`) or has a `GainF2` step, there is no minimal
counterexample. -/
theorem no_minCE_of_gainF2_or_cubeLocal
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q → CubeLocal gates p Q ∨ ∃ v, v ∉ Q ∧ GainF2 gates S Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, hN, hQ⟩ := H n m S gates out M
  have hb := base_le_F2_pts_or gates S (fun Q hpos => (hQ Q hpos).imp_left fun hL =>
    baseDQ_le_F2_of_cubeLocal gates p hp M.ce.hg M.ce.hU hN S out Q M.ce.hS M.ce.hev hL) _ ∅ le_rfl
  rw [baseDQ_empty] at hb
  have h2 := card_F2_le gates S ∅
  have h3 := M.ce.hlt
  omega

/-- **951 from the F2 step with the three local closures**: if every minimal counterexample has a NOT
gate such that every `Q` with positive base is `CubeLocal`, satisfies LW1, or has a `GainF2` step, there
is no minimal counterexample. -/
theorem no_minCE_of_gainF2_or_local
    (H : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
        ∀ Q, 0 < baseDQ S ∅ Q →
          CubeLocal gates p Q ∨ LW1 gates p S Q ∨ ∃ v, v ∉ Q ∧ GainF2 gates S Q v) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  intro n m S gates out M
  obtain ⟨p, hp, hN, hQ⟩ := H n m S gates out M
  have hb := base_le_F2_pts_or gates S (fun Q hpos => by
    rcases hQ Q hpos with hL | hL | hG
    · exact Or.inl (baseDQ_le_F2_of_cubeLocal gates p hp M.ce.hg M.ce.hU hN S out Q M.ce.hS
        M.ce.hev hL)
    · exact Or.inl (baseDQ_le_F2_of_LW1 gates p hp M.ce.hg M.ce.hU hN S out Q M.ce.hev hL)
    · exact Or.inr hG) _ ∅ le_rfl
  rw [baseDQ_empty] at hb
  have h2 := card_F2_le gates S ∅
  have h3 := M.ce.hlt
  omega

end PEqualNP.Outside.L_meta_951_aux
