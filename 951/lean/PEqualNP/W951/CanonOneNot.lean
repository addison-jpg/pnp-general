import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.CanonClass
import PEqualNP.W951.Lift
import PEqualNP.W951.Count

/-!
# CanonOneNot: the canonical classes `K_1(w)`, `K_0(w; m)` of a one-NOT circuit (GM, W0, W1, X)

The one-NOT instance of `CanonClass.lean` (`951/PROOF_PLAN_SUGGESTIONS.md` §2, refereed): the
monotone gate list is the lift `lift n p gates` (`Lift.lean`) of a circuit `gates` on `n` inputs
whose gate `p` is the NOT gate, on `N = n + 1` inputs, the last input `y = Fin.last n` standing for
the value of the NOT gate. `C_1` is the lift at `y = 1`, `C_0` the lift at `y = 0`. For a set `R`
(`R = S_w`), `top_w = Zof R` (true exactly off `R`) and `d_w = |R| - 1`:

* `K1 gates p R` (world 1): OR gates `g` of the lift with `C_1(g)(top_w) = 0` and
  `C_1(g)(e_u) = 1` for two `u ∈ R` or more;
* `K0 gates p R m` (world 0, `m` a point with `h(m) = 1`, i.e. the NOT gate `0` at `m`):
  OR gates `g` with `C_0(g)(top_w) = 0` and `C_0(g)(m + e_u) = 1` for two `u ∈ R` or more.

Both are `Finset`s of REAL wires (`realWire`: the lifted gate `j` is the real wire `n + j` before
the NOT and `n + j + 1` after it; the convention of `mergeSet`). Results:

* `card_K1` (W1 size): `h(top_w) = 0` (the NOT gate is `1` at `top_w`) ⇒ `d_w ≤ |K_1(w)|`. No
  condition on heavy points (referee 10:39).
* `card_K0` (W0 size): `m ∩ R = ∅` and `h(m) = 1` ⇒ `d_w ≤ |K_0(w; m)|`.
* `disjoint_K1` (W1): `K_1(w) ∩ K_1(w') = ∅` for `|S_w ∩ S_w'| ≤ 1`.
* `disjoint_K0` (W0): `K_0(w; m) ∩ K_0(w'; m') = ∅` once `m ∩ S_w' = ∅` (ONE side suffices).
* `disjoint_K0_K1` (D across worlds): `K_0(w; m) ∩ K_1(w') = ∅` once `m ∩ S_w' = ∅`.
* `cross_K1_K0` (X): a wire in `K_1(w) ∩ K_0(w'; m')` is `1` at `e_u` with `y = 1` and `0` at `e_u`
  with `y = 0` for some `u ∈ S_w`: it depends on the NOT gate. By `disjoint_K0_K1` this case
  needs `m' ∩ S_w ≠ ∅`.

The sizes use correctness of the output `o` (`val gates x o = OR_R(x)`) through `val_lift` and
`lift_exact`; the disjointness statements use only that the lift is monotone.
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section CanonOneNot

variable {n : ℕ}

/-! ## Wires and points -/

/-- The real wire of gate `j` of the lift: `n + j` before the NOT gate, `n + j + 1` after it. -/
def realWire (n p j : ℕ) : ℕ := if j < p then n + j else n + j + 1

theorem realWire_injective (n p : ℕ) : Function.Injective (realWire n p) := by
  intro a b h
  unfold realWire at h
  split_ifs at h <;> omega

theorem liftWire_realWire (n p j : ℕ) : liftWire n p (realWire n p j) = n + 1 + j := by
  unfold liftWire realWire
  split_ifs <;> omega

/-- An enumeration of a finset of coordinates. -/
noncomputable def enumF (R : Finset (Fin n)) (t : Fin R.card) : Fin n := (R.equivFin.symm t : Fin n)

theorem enumF_injective (R : Finset (Fin n)) : Function.Injective (enumF R) :=
  fun _ _ h => R.equivFin.symm.injective (Subtype.ext h)

theorem enumF_mem (R : Finset (Fin n)) (t : Fin R.card) : enumF R t ∈ R :=
  (R.equivFin.symm t).2

/-- A set of real coordinates as a set of lifted coordinates. -/
def liftSet (R : Finset (Fin n)) : Finset (Fin (n + 1)) := R.map Fin.castSuccEmb

theorem mem_liftSet {R : Finset (Fin n)} {c : Fin n} : Fin.castSucc c ∈ liftSet R ↔ c ∈ R := by
  simp [liftSet]

theorem last_not_mem_liftSet (R : Finset (Fin n)) : Fin.last n ∉ liftSet R := by
  simp [liftSet, Fin.castSucc_ne_last]

theorem ext_castSucc (x : Fin n → Bool) (y : Bool) (c : Fin n) : ext x y (Fin.castSucc c) = x c := by
  simp [ext]

theorem ext_last (x : Fin n → Bool) (y : Bool) : ext x y (Fin.last n) = y := by
  simp [ext]

theorem ext_canonPt_false (A : Finset (Fin n)) : ext (canonPt A) false = canonPt (liftSet A) := by
  funext c
  induction c using Fin.lastCases with
  | last => rw [ext_last]; simp [canonPt, last_not_mem_liftSet]
  | cast c => rw [ext_castSucc]; simp [canonPt, mem_liftSet]

theorem ext_canonPt_true (A : Finset (Fin n)) :
    ext (canonPt A) true = canonPt (insert (Fin.last n) (liftSet A)) := by
  funext c
  induction c using Fin.lastCases with
  | last => rw [ext_last]; simp [canonPt]
  | cast c =>
    rw [ext_castSucc]
    simp [canonPt, mem_liftSet, Fin.castSucc_ne_last]

/-- World-1 atom `e_u` (with `y = 1`). -/
theorem atom1_eq (u : Fin n) :
    canonPt (insert (Fin.castSucc u) {Fin.last n}) = ext (canonPt {u}) true := by
  rw [ext_canonPt_true, liftSet, Finset.map_singleton, Fin.castSuccEmb_apply, Finset.pair_comm]

/-- World-0 atom `m + e_u` (with `y = 0`). -/
theorem atom0_eq (u : Fin n) (m : Finset (Fin n)) :
    canonPt (insert (Fin.castSucc u) (liftSet m)) = ext (canonPt (insert u m)) false := by
  rw [ext_canonPt_false]
  congr 1
  simp [liftSet, Finset.map_insert]

/-- `ext top_w y` is false only on `R` (and on `y` when `y = 0`). -/
theorem ext_Zof_false (R : Finset (Fin n)) (b : Bool) (c : Fin (n + 1))
    (hc : ext (Zof R) b c = false) : c ∈ liftSet R ∨ c ∈ ({Fin.last n} : Finset (Fin (n + 1))) := by
  induction c using Fin.lastCases with
  | last => exact Or.inr (Finset.mem_singleton_self _)
  | cast c =>
    rw [ext_castSucc] at hc
    left
    rw [mem_liftSet]
    simpa [Zof] using hc

theorem ext_Zof_true (R : Finset (Fin n)) (c : Fin (n + 1))
    (hc : ext (Zof R) true c = false) : c ∈ liftSet R ∨ c ∈ (∅ : Finset (Fin (n + 1))) := by
  rcases ext_Zof_false R true c hc with h | h
  · exact Or.inl h
  · rw [Finset.mem_singleton.mp h, ext_last] at hc
    exact absurd hc (by decide)

theorem disjoint_liftSet {R R' : Finset (Fin n)} (h : Disjoint R R') :
    Disjoint (liftSet R) (liftSet R') := by
  rw [liftSet, liftSet, Finset.disjoint_map]
  exact h

theorem card_liftSet_inter (R R' : Finset (Fin n)) :
    (liftSet R ∩ liftSet R').card = (R ∩ R').card := by
  rw [liftSet, liftSet, ← Finset.map_inter, Finset.card_map]

theorem disjoint_liftSet_last (R : Finset (Fin n)) :
    Disjoint (liftSet R) ({Fin.last n} : Finset (Fin (n + 1))) :=
  Finset.disjoint_singleton_right.mpr (last_not_mem_liftSet R)

/-! ## The classes -/

/-- **`K_1(w)`** (world 1), as real wires: OR gates of the lift that are `0` at `(top_w, 1)` and
`1` at `(e_u, 1)` for two `u ∈ R` or more. -/
noncomputable def K1 (gates : List Gate) (p : ℕ) (R : Finset (Fin n)) : Finset ℕ :=
  (orClz (lift n p gates) (ext (Zof R) true)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) {Fin.last n}))).image (realWire n p)

/-- **`K_0(w; m)`** (world 0), as real wires: OR gates of the lift that are `0` at `(top_w, 0)` and
`1` at `(m + e_u, 0)` for two `u ∈ R` or more. -/
noncomputable def K0 (gates : List Gate) (p : ℕ) (R m : Finset (Fin n)) : Finset ℕ :=
  (orClz (lift n p gates) (ext (Zof R) false)
    (fun t => canonPt (insert (Fin.castSucc (enumF R t)) (liftSet m)))).image (realWire n p)

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
theorem monoList_lift : MonoList (lift n p gates) :=
  lift_ops (n := n) gates p hp hg hU hN

include hg hU hN in
/-- The NOT gate is antitone: `0` at `x` stays `0` above `x` (its input `h` is monotone). -/
theorem not_false_of_le {x x' : Fin n → Bool} (hle : x ≤ x')
    (h : val gates x (n + p) = false) : val gates x' (n + p) = false := by
  have hops : ∀ g ∈ gates.take p, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hgm
    have hkp : k < p := by simp at hk; omega
    have hk' : k < gates.length := by simp at hk; omega
    rw [List.getElem_take]
    rcases (hg (gates[k]'hk') (List.getElem_mem hk')).1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (hU k p _ hp h1 hN) (by omega)
  rw [val_not gates p hp hN] at h ⊢
  have hv := val_le_of_le (gates.take p) hops hle (notIn n p gates)
  rw [Bool.not_eq_false'] at h
  rw [h] at hv
  rw [Bool.not_eq_false']
  revert hv
  cases val (gates.take p) x' (notIn n p gates) <;> decide

/-! ## GM: the sizes -/

include hg hU hN in
/-- **W1 size.** If the NOT gate is `1` at `top_w` (`h(top_w) = 0`) and `o` computes `OR_R`,
then `|K_1(w)| ≥ d_w = |R| - 1`. -/
theorem card_K1 (R : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true))
    (hν : val gates (Zof R) (n + p) = true) : R.card - 1 ≤ (K1 gates p R).card := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hzo : val (lift n p gates) (ext (Zof R) true) (liftWire n p o) = false := by
    have hl := val_lift (n := n) gates p hp (Zof R) o
    rw [hν, hev] at hl
    rw [← hl]
    simp [Zof]
  have hao : ∀ t, val (lift n p gates) (canonPt (insert (Fin.castSucc (enumF R t)) {Fin.last n}))
      (liftWire n p o) = true := by
    intro t
    rw [atom1_eq]
    refine (lift_exact (n := n) gates p hp hg hU hN (canonPt {enumF R t}) o).2.1 ?_
    rw [hev]
    exact decide_eq_true ⟨enumF R t, enumF_mem R t, canonPt_eq_true.mpr (Finset.mem_singleton_self _)⟩
  obtain ⟨M, hM, hk⟩ := canon_size_pt (lift n p gates) hm (liftSet R) {Fin.last n} ∅
    (Finset.disjoint_singleton_left.mpr (last_not_mem_liftSet R)) (Finset.disjoint_empty_right _)
    (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h)) (ext (Zof R) true)
    (ext_Zof_true R) (liftWire n p o) hzo hao
  rw [K1, Finset.card_image_of_injective _ (realWire_injective n p)]
  exact hk.trans (Finset.card_le_card hM)

include hg hU hN in
/-- **W0 size.** If `m ∩ R = ∅`, the NOT gate is `0` at `m` (`h(m) = 1`, e.g. `m` a minterm of
`h`) and `o` computes `OR_R`, then `|K_0(w; m)| ≥ d_w = |R| - 1`. -/
theorem card_K0 (R m : Finset (Fin n)) (hmR : Disjoint m R) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true))
    (hmN : val gates (canonPt m) (n + p) = false) : R.card - 1 ≤ (K0 gates p R m).card := by
  classical
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hzo : val (lift n p gates) (ext (Zof R) false) (liftWire n p o) = false := by
    have h1 := (lift_exact (n := n) gates p hp hg hU hN (Zof R) o).1
    cases hv : val (lift n p gates) (ext (Zof R) false) (liftWire n p o)
    · rfl
    · have := h1 hv
      rw [hev] at this
      simp [Zof] at this
  have hao : ∀ t, val (lift n p gates) (canonPt (insert (Fin.castSucc (enumF R t)) (liftSet m)))
      (liftWire n p o) = true := by
    intro t
    rw [atom0_eq]
    have hle : canonPt m ≤ canonPt (insert (enumF R t) m) := by
      intro c
      refine Bool.le_iff_imp.mpr fun hc => ?_
      exact canonPt_eq_true.mpr (Finset.mem_insert_of_mem (canonPt_eq_true.mp hc))
    have hν := not_false_of_le gates p hp hg hU hN hle hmN
    have hl := val_lift (n := n) gates p hp (canonPt (insert (enumF R t) m)) o
    rw [hν] at hl
    rw [← hl, hev]
    exact decide_eq_true ⟨enumF R t, enumF_mem R t,
      canonPt_eq_true.mpr (Finset.mem_insert_self _ _)⟩
  obtain ⟨M, hM, hk⟩ := canon_size_pt (lift n p gates) hm (liftSet R) (liftSet m) {Fin.last n}
    (disjoint_liftSet hmR) (disjoint_liftSet_last m)
    (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h)) (ext (Zof R) false)
    (ext_Zof_false R false) (liftWire n p o) hzo hao
  rw [K0, Finset.card_image_of_injective _ (realWire_injective n p)]
  exact hk.trans (Finset.card_le_card hM)

/-! ## W0, W1, D, X: disjointness -/

include hg hU hN in
/-- **W1.** `K_1(w) ∩ K_1(w') = ∅` for `|S_w ∩ S_w'| ≤ 1`. -/
theorem disjoint_K1 (R R' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1) :
    Disjoint (K1 gates p R) (K1 gates p R') := by
  classical
  rw [K1, K1, Finset.disjoint_image (realWire_injective n p)]
  exact canon_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) (liftSet R) (liftSet R')
    {Fin.last n} ∅ (by rw [card_liftSet_inter]; exact hRR)
    (Finset.disjoint_singleton_left.mpr (last_not_mem_liftSet R')) (Finset.disjoint_empty_right _)
    (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h))
    (fun t => mem_liftSet.mpr (enumF_mem R t)) (fun _ => Finset.notMem_empty _)
    (ext (Zof R) true) (ext (Zof R') true) (ext_Zof_true R') _

include hg hU hN in
/-- **W0.** `K_0(w; m) ∩ K_0(w'; m') = ∅` for `|S_w ∩ S_w'| ≤ 1` once `m ∩ S_w' = ∅`. -/
theorem disjoint_K0 (R R' m m' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1)
    (hmR' : Disjoint m R') : Disjoint (K0 gates p R m) (K0 gates p R' m') := by
  classical
  rw [K0, K0, Finset.disjoint_image (realWire_injective n p)]
  exact canon_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) (liftSet R) (liftSet R')
    (liftSet m) {Fin.last n} (by rw [card_liftSet_inter]; exact hRR) (disjoint_liftSet hmR')
    (disjoint_liftSet_last m) (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h))
    (fun t => mem_liftSet.mpr (enumF_mem R t))
    (fun t => Finset.notMem_singleton.mpr (Fin.castSucc_ne_last _))
    (ext (Zof R) false) (ext (Zof R') false) (ext_Zof_false R' false) _

include hg hU hN in
/-- **D across worlds.** `K_0(w; m) ∩ K_1(w') = ∅` for `|S_w ∩ S_w'| ≤ 1` once `m ∩ S_w' = ∅`. -/
theorem disjoint_K0_K1 (R R' m : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1)
    (hmR' : Disjoint m R') : Disjoint (K0 gates p R m) (K1 gates p R') := by
  classical
  rw [K0, K1, Finset.disjoint_image (realWire_injective n p)]
  exact canon_disjoint (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) (liftSet R) (liftSet R')
    (liftSet m) {Fin.last n} (by rw [card_liftSet_inter]; exact hRR) (disjoint_liftSet hmR')
    (disjoint_liftSet_last m) (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h))
    (fun t => mem_liftSet.mpr (enumF_mem R t))
    (fun t => Finset.notMem_singleton.mpr (Fin.castSucc_ne_last _))
    (ext (Zof R) false) (ext (Zof R') true) (ext_Zof_false R' true) _

include hg hU hN in
/-- **X.** A wire `i` in `K_1(w) ∩ K_0(w'; m')` (`|S_w ∩ S_w'| ≤ 1`) depends on the NOT gate: for
some `u ∈ S_w` its lifted value at `e_u` is `1` with `y = 1` and `0` with `y = 0`. -/
theorem cross_K1_K0 (R R' m' : Finset (Fin n)) (hRR : (R ∩ R').card ≤ 1) {i : ℕ}
    (hi : i ∈ K1 gates p R) (hi' : i ∈ K0 gates p R' m') :
    ∃ u ∈ R, val (lift n p gates) (ext (canonPt {u}) true) (liftWire n p i) = true ∧
      val (lift n p gates) (ext (canonPt {u}) false) (liftWire n p i) = false := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨j', hj', hjj⟩ := Finset.mem_image.mp hi'
  rw [realWire_injective n p hjj] at hj'
  obtain ⟨t, h1, h0⟩ := canon_cross (lift n p gates) (monoList_lift (n := n) gates p hp hg hU hN) (liftSet R)
    (liftSet R') {Fin.last n} ∅ {Fin.last n} (by rw [card_liftSet_inter]; exact hRR)
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _)
    (fun t => Fin.castSucc (enumF R t))
    (fun s t h => enumF_injective R (Fin.castSucc_injective n h))
    (fun t => mem_liftSet.mpr (enumF_mem R t))
    (fun t => Finset.notMem_singleton.mpr (Fin.castSucc_ne_last _))
    (ext (Zof R) true) (ext (Zof R') false) (ext_Zof_false R' false) _ hj hj'
  refine ⟨enumF R t, enumF_mem R t, ?_, ?_⟩
  · rw [← atom1_eq, liftWire_realWire]
    exact h1
  · have he : ext (canonPt {enumF R t}) false =
        canonPt (insert (Fin.castSucc (enumF R t)) (∅ : Finset (Fin (n + 1)))) := by
      rw [ext_canonPt_false, liftSet, Finset.map_singleton, Fin.castSuccEmb_apply,
        Finset.insert_empty]
    rw [he, liftWire_realWire]
    exact h0

end CanonOneNot

end PEqualNP.Outside.L_meta_951_aux
