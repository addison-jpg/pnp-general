import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2Induct
import PEqualNP.W951.F2Bridge
import PEqualNP.W951.GraphHeavyF2
import PEqualNP.W951.MinCE

/-!
# NotVarF2: the case `h = x_a` (the NOT gate reads an input) ⇒ `base ≤ |F2(∅)|`

Front A2 (12:55, proof checked by front): if the NOT gate of a one-NOT circuit computes `¬x_a` for an
input `a`, the sets have a lifted SDR whose classes lie in F2, so `∑_w (|S_w| - 1) ≤ |F2(∅)|`. This
needs no minimality, only correct outputs and `|S_w ∩ S_w'| ≤ 1`.

The lifted test system of `R` (`xvLTS a R`): zero point `(top, 1)` with `top = Zof (R ∪ {a})` (`1`
outside `R ∪ {a}`), atoms `(e_u, [u ≠ a])`. Both are the `ν`-lifts of the real points (`ν x = ¬x_a`):
`ν(top) = 1` since `top_a = 0`, and `ν(e_u) = [u ≠ a]`. For a star set (`a ∈ R`) this is front's
`(top_w, 1)`, `(e_u, 1)`, `(e_a, 0)`; for a non-star set it is `(top_w \ {a}, 1)`, `(e_u, 1)`.

* `val_not_of_head`: a NOT gate whose first input is the input wire `a` computes `¬x_a`.
* `xvLTS_valid`: validity (the real outputs at `top`, `e_u`, read through `val_lift`).
* `xv_pairs`, `xvLTS_disjoint`: for `|R ∩ R'| ≤ 1`, one of the two directions of the lifted Theorem U
  holds (`a ∈ R'`: the atoms of `R` meet `R'` in at most one point; `a ∉ R'`: the atoms of `R'` meet
  `R ∪ {a}` in at most one point), so the classes are disjoint.
* `lowerWire_mem_F2_xv`: every gate of the class of `R = S_w` is a real F2 gate at `Q = ∅`: an OR gate
  (merges are OR gates) with the real witness `(top, u, u')`, since `top` is in world 1 and the atoms
  `(e_u, [u ≠ a])` lie below the lifts `ν(top + e_u)`.
* **`muF2_of_notVar`**: `MUF2 S gates` (`base ≤ |F2(∅)|`).
* **`IsCE.false_of_notVar`**, **`MinCE.not_notVar`**: no counterexample (minimal or not) has its NOT
  gate computing an input literal.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section NotVarF2

variable {n m : ℕ}

/-- The lifted atom of `u` in the variable case: `(e_u, [u ≠ a])`. -/
def xvAtom (a : Fin n) (c : Fin (n + 1)) : Fin (n + 1) → Bool :=
  if h : c = Fin.last n then canonPt ∅
  else ext (canonPt {c.castPred h}) (decide (c.castPred h ≠ a))

theorem xvAtom_castSucc (a u : Fin n) :
    xvAtom a (Fin.castSucc u) = ext (canonPt {u}) (decide (u ≠ a)) := by
  rw [xvAtom, dite_eq_right (Fin.castSucc_ne_last u), Fin.castPred_castSucc]

/-- **The lifted test system of `R` when the NOT gate computes `¬x_a`**: zero point
`(Zof (R ∪ {a}), 1)`, atoms `(e_u, [u ≠ a])`. -/
def xvLTS (a : Fin n) (R : Finset (Fin n)) : LTS n :=
  ⟨ext (Zof (insert a R)) true, xvAtom a⟩

theorem Zof_insert_self (a : Fin n) (R : Finset (Fin n)) : Zof (insert a R) a = false := by
  simp [Zof]

theorem Zof_insert_of_mem {a : Fin n} {R : Finset (Fin n)} {u : Fin n} (hu : u ∈ R) :
    Zof (insert a R) u = false := by
  simp [Zof, hu]

/-- **The variable pairs**: for `|R ∩ R'| ≤ 1`, either every two points of `R` have one outside
`R' ∪ {a}`, or every two points of `R'` have one outside `R ∪ {a}`. -/
theorem xv_pairs (a : Fin n) {R R' : Finset (Fin n)} (hRR : (R ∩ R').card ≤ 1) :
    (∀ u ∈ R, ∀ v ∈ R, u ≠ v → u ∉ insert a R' ∨ v ∉ insert a R') ∨
      (∀ u ∈ R', ∀ v ∈ R', u ≠ v → u ∉ insert a R ∨ v ∉ insert a R) := by
  classical
  by_cases haR' : a ∈ R'
  · left
    intro u hu v hv huv
    rw [Finset.insert_eq_of_mem haR']
    by_contra h
    push Not at h
    have : 1 < (R ∩ R').card :=
      Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, h.1⟩, v, Finset.mem_inter.mpr ⟨hv, h.2⟩,
        huv⟩
    omega
  · right
    intro u hu v hv huv
    by_contra h
    push Not at h
    have hu' : u ∈ R := (Finset.mem_insert.mp h.1).resolve_left fun h' => haR' (h' ▸ hu)
    have hv' : v ∈ R := (Finset.mem_insert.mp h.2).resolve_left fun h' => haR' (h' ▸ hv)
    have : 1 < (R ∩ R').card :=
      Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu', hu⟩, v, Finset.mem_inter.mpr ⟨hv', hv⟩,
        huv⟩
    omega

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)
  (a : Fin n) (hh : ∀ x : Fin n → Bool, val gates x (n + p) = !x a)

include hN in
/-- A NOT gate whose first input is the input wire `a` computes `¬x_a`. -/
theorem val_not_of_head (ha : (gates[p]'hp).inputs.head? = some (a : ℕ)) :
    ∀ x : Fin n → Bool, val gates x (n + p) = !x a := by
  intro x
  rw [val_gate gates x p hp, hN]
  obtain ⟨rest, hrest⟩ : ∃ rest, (gates[p]'hp).inputs = (a : ℕ) :: rest := by
    cases h : (gates[p]'hp).inputs with
    | nil => rw [h] at ha; exact absurd ha (by simp)
    | cons j rest =>
      rw [h, List.head?_cons, Option.some_inj] at ha
      exact ⟨rest, by rw [ha]⟩
  rw [hrest, List.map_cons, val_input _ x a a.isLt]
  rfl

include hh in
theorem nuPt_of_var (x : Fin n → Bool) : nuPt gates p x = ext x (!x a) := by
  rw [nuPt, hh]

include hp hh in
/-- **Validity** of the variable test system (the outputs are correct). -/
theorem xvLTS_valid (R : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true)) :
    LTSValid gates p R o (xvLTS a R) := by
  refine ⟨?_, fun c hc => ?_, fun x hx c hc c' hc' h1 h2 => ?_⟩
  · show val (lift n p gates) (ext (Zof (insert a R)) true) (liftWire n p o) = false
    have key := val_lift (n := n) gates p hp (Zof (insert a R)) o
    rw [hh, Zof_insert_self, hev, Bool.not_false] at key
    rw [← key]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    rw [Zof_insert_of_mem hv] at hzv
    exact absurd hzv (by decide)
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    show val (lift n p gates) (xvAtom a (Fin.castSucc u)) (liftWire n p o) = true
    rw [xvAtom_castSucc]
    have key := val_lift (n := n) gates p hp (canonPt {u}) o
    have hy : (!canonPt {u} a) = decide (u ≠ a) := by
      by_cases hua : u = a
      · subst hua; simp [canonPt]
      · simp [canonPt, Ne.symm hua, hua]
    rw [hh, hy, hev] at key
    rw [← key]
    exact decide_eq_true ⟨u, hu, canonPt_eq_true.mpr (Finset.mem_singleton_self u)⟩
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp hc'
    change ext (Zof (insert a R)) true x = false at hx
    change xvAtom a (Fin.castSucc u) x = true at h1
    change xvAtom a (Fin.castSucc v) x = true at h2
    rw [xvAtom_castSucc] at h1 h2
    induction x using Fin.lastCases with
    | last =>
      rw [ext_last] at hx
      exact absurd hx (by decide)
    | cast y =>
      rw [ext_castSucc] at h1 h2
      have e1 := Finset.mem_singleton.mp (canonPt_eq_true.mp h1)
      have e2 := Finset.mem_singleton.mp (canonPt_eq_true.mp h2)
      rw [← e1, ← e2]

/-- The atom of a point outside `R' ∪ {a}` lies below the zero point of `R'`. -/
theorem xvAtom_le_zero {R' : Finset (Fin n)} {u : Fin n} (hu : u ∉ insert a R') :
    xvAtom a (Fin.castSucc u) ≤ (xvLTS a R').zero := by
  rw [xvAtom_castSucc]
  refine ext_le_of_le (canonPt_le fun x hx => ?_) (Bool.le_true _)
  rw [Finset.mem_singleton.mp hx]
  simp [Zof, hu]

include hp hg hU hN in
/-- **Disjointness** (lifted Theorem U, one direction) from the variable pairs. -/
theorem xvLTS_disjoint_of_pairs (R R' : Finset (Fin n))
    (h : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → u ∉ insert a R' ∨ v ∉ insert a R') :
    Disjoint (ltsCls gates p R (xvLTS a R)) (ltsCls gates p R' (xvLTS a R')) := by
  refine runMT_disjoint_of_le _ (monoList_lift (n := n) gates p hp hg hU hN) _ _ _ _ _ _
    (liftSet_pairs fun u hu v hv huv => ?_)
  rcases h u hu v hv huv with h1 | h1
  · exact Or.inl (xvAtom_le_zero a h1)
  · exact Or.inr (xvAtom_le_zero a h1)

include hp hg hU hN in
/-- **The variable classes of two sets meeting in at most one point are disjoint.** -/
theorem xvLTS_disjoint (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1) :
    Disjoint (ltsCls gates p R (xvLTS a R)) (ltsCls gates p R' (xvLTS a R')) := by
  rcases xv_pairs a hRR with h | h
  · exact xvLTS_disjoint_of_pairs gates p hp hg hU hN a R R' h
  · exact (xvLTS_disjoint_of_pairs gates p hp hg hU hN a R' R h).symm

/-- The atoms of the variable test system lie inside `zero ∪ {u}`. -/
theorem xv_hT (R : Finset (Fin n)) :
    ∀ c ∈ liftSet R, ∀ c' : Fin (n + 1), (xvLTS a R).atom c c' = true →
      (xvLTS a R).zero c' = false → c' = c := by
  intro c hc c' h1 h2
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  change xvAtom a (Fin.castSucc u) c' = true at h1
  change ext (Zof (insert a R)) true c' = false at h2
  rw [xvAtom_castSucc] at h1
  induction c' using Fin.lastCases with
  | last =>
    rw [ext_last] at h2
    exact absurd h2 (by decide)
  | cast y =>
    rw [ext_castSucc] at h1
    rw [Finset.mem_singleton.mp (canonPt_eq_true.mp h1)]

include hp hg hU hN hh in
/-- **The variable classes lie in F2**: the real wire of a gate of the class of `S_w` is an OR gate of
the real circuit with the real witness `(Zof (S_w ∪ {a}), u, u')` at `Q = ∅`. -/
theorem lowerWire_mem_F2_xv (S : Fin m → Finset (Fin n)) (w : Fin m) {i : ℕ}
    (hi : i ∈ ltsCls gates p (S w) (xvLTS a (S w))) : lowerWire n p i ∈ F2 gates S ∅ := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  obtain ⟨j, rfl, hor⟩ := runMT_or _ _ _ _ hm (xv_hT a (S w)) hi
  have h1 := run_sub_DT _ _ _ _ _ hi
  rw [DT, Finset.mem_filter, Finset.mem_Ico] at h1
  obtain ⟨⟨-, hjl⟩, hz, c, c', hcc, hc, hc', h1c, h1c'⟩ := h1
  obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
  obtain ⟨u', hu', rfl⟩ := mem_liftSet_iff.mp hc'
  have hjl' : j < (lift n p gates).length := by omega
  obtain ⟨k, hk, hork⟩ := lowerWire_isOr gates p hp hjl' hor
  have hge : n + 1 ≤ n + 1 + j := by omega
  set Z := Zof (insert a (S w)) with hZ
  -- the atom of `u` lies below the lift of `Z + e_u`
  have hatom : ∀ t ∈ S w, xvAtom a (Fin.castSucc t) ≤ nuPt gates p (Function.update Z t true) := by
    intro t ht
    rw [xvAtom_castSucc, nuPt_of_var gates p a hh]
    refine ext_le_of_le (canonPt_le fun x hx => ?_) ?_
    · rw [Finset.mem_singleton.mp hx]
      simp
    · by_cases hta : t = a
      · subst hta
        simp
      · rw [Function.update_of_ne (Ne.symm hta), hZ, Zof_insert_self]
        exact Bool.le_true _
  refine mem_F2.mpr ⟨⟨k, hk, hork⟩, w, mem_aliveSets.mpr (Finset.disjoint_empty_right _), Z, u, u',
    hu, hu', fun h => hcc (h ▸ rfl), fun x hx => Zof_insert_of_mem hx,
    fun x hx => absurd hx (Finset.notMem_empty x), ?_, ?_, ?_⟩
  · refine real_zero_of_lift gates p hp hg hU hN hge (ζ := ext Z true) ?_ hz
    rw [nuPt_of_var gates p a hh, hZ, Zof_insert_self]
    rfl
  · exact real_one_of_lift gates p hp hg hU hN hge (hatom u hu) h1c
  · exact real_one_of_lift gates p hp hg hU hN hge (hatom u' hu') h1c'

include hp hg hU hN hh in
/-- **Front A2, case `h = x_a`**: if the NOT gate computes `¬x_a`, the outputs are correct and the
sets meet pairwise in at most one point, then `base ≤ |F2(∅)|`. No minimality. -/
theorem muF2_of_notVar (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) :
    MUF2 S gates := by
  classical
  set C : Fin m → Finset ℕ := fun w => ltsCls gates p (S w) (xvLTS a (S w)) with hC
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint C :=
    fun w _ w' _ hww => xvLTS_disjoint gates p hp hg hU hN a (S w) (S w') (hS w w' hww)
  have hinj : Set.InjOn (lowerWire n p) ↑(Finset.univ.biUnion C) := by
    intro i hi i' hi' h
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hi)
    obtain ⟨w', -, hw'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hi')
    have r := Finset.mem_Ico.mp (ltsCls_subset gates p (S w) _ hw)
    have r' := Finset.mem_Ico.mp (ltsCls_subset gates p (S w') _ hw')
    exact lowerWire_injOn r.1 r'.1 h
  unfold MUF2
  calc ∑ w, ((S w).card - 1)
      ≤ ∑ w, (C w).card := Finset.sum_le_sum fun w _ =>
        card_ltsCls gates p hp hg hU hN (S w) (out w) _
          (xvLTS_valid gates p hp a hh (S w) (out w) (hev w))
    _ = (Finset.univ.biUnion C).card := (Finset.card_biUnion hpd).symm
    _ = ((Finset.univ.biUnion C).image (lowerWire n p)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (F2 gates S ∅).card := Finset.card_le_card fun g hg' => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg'
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        exact lowerWire_mem_F2_xv gates p hp hg hU hN a hh S w hw

end NotVarF2

/-- **No counterexample has its NOT gate computing an input literal** (front A2, case `h = x_a`):
`base ≤ |F2(∅)| ≤ s < base`. -/
theorem IsCE.false_of_notVar {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (C : IsCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) (a : Fin n)
    (hh : ∀ x : Fin n → Bool, val gates x (n + p) = !x a) : False := by
  have h1 := muF2_of_notVar gates p hp C.hg C.hU hN a hh S out C.hS C.hev
  have h2 := card_F2_le gates S ∅
  have h3 := C.hlt
  unfold MUF2 at h1
  omega

/-- **In a minimal counterexample the NOT gate does not read an input wire first.** -/
theorem MinCE.not_notVar {n m : ℕ} {S : Fin m → Finset (Fin n)} {gates : List Gate}
    {out : Fin m → ℕ} (M : MinCE S gates out) (p : ℕ) (hp : p < gates.length)
    (hN : (gates[p]'hp).op = GateOp.not) (a : Fin n)
    (ha : (gates[p]'hp).inputs.head? = some (a : ℕ)) : False :=
  M.ce.false_of_notVar p hp hN a (val_not_of_head gates p hp hN a ha)

end PEqualNP.Outside.L_meta_951_aux
