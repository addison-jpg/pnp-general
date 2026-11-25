import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.PureGP
import PEqualNP.W951.MergeSDR

/-!
# PureLLift: real merge sets are lifted test systems (front A1's L-LIFT, 12:20)

The real merge set `M_z(w) = mergeSet gates R z` of a one-NOT circuit (NOT gate at `p`) is the class of
a VALID lifted test system (`LTS`, `PureGP.lean`): zero point `(z, ν z)` and atoms `(z + e_u, ν(z + e_u))`,
`ν x` = the NOT gate's value at `x` (`realLTS`), read back in real wire numbers (`lowerWire`).

* `run_lift`: the union-find run of the real circuit at `(z, z + e_u)` and the run of the lift at the
  lifted points agree gate for gate: labels through `Fin.castSucc`, merge sets through `lowerWire`.
  The NOT gate never merges (it is `1` at `z`, or `0` at `z` and then at every `z + e_u`).
* `mergeSet_eq_lift`: `M_z(w) = (ltsCls gates p R (realLTS gates p z)).image (lowerWire n p)`.
* `realLTS_valid`: at a zero point of `R` with `o` computing `OR_R`, the lifted real test system is
  valid (atoms separated outside the zero point: `z + e_u` differs from `z` only at `u`, and `ν` is
  antitone).
* `liftSDR_of_mergeSDR`, `muL_of_mergeSDR`: MergeSDR ⇒ LiftSDR ⇒ MUL. So the lifted targets are
  WEAKER than the old MergeSDR target (front A1: the pure lists are too narrow, `cxMU_dd`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section LLift

variable {n : ℕ}

/-- `(x, ν x)`: a real point with the NOT gate's value as `y`. -/
def nuPt (gates : List Gate) (p : ℕ) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  ext x (val gates x (n + p))

/-- The lifted atoms of the real test system at `z`: the atom of `u` is `(z + e_u, ν(z + e_u))`. -/
def realAtoms (gates : List Gate) (p : ℕ) (z : Fin n → Bool) (c : Fin (n + 1)) : Fin (n + 1) → Bool :=
  if h : c = Fin.last n then canonPt ∅ else nuPt gates p (upPt z (c.castPred h))

theorem realAtoms_castSucc (gates : List Gate) (p : ℕ) (z : Fin n → Bool) (u : Fin n) :
    realAtoms gates p z (Fin.castSucc u) = nuPt gates p (upPt z u) := by
  rw [realAtoms, dite_eq_right (Fin.castSucc_ne_last u), Fin.castPred_castSucc]

/-- **The real test system at `z`, lifted.** -/
def realLTS (gates : List Gate) (p : ℕ) (z : Fin n → Bool) : LTS n :=
  ⟨nuPt gates p z, realAtoms gates p z⟩

/-- The lifted gate of real gate `k ≠ p`. -/
def notSkipIdx (p k : ℕ) : ℕ := if k < p then k else k - 1

/-- The number of lifted gates among the first `k` real gates. -/
def notSkipCnt (p k : ℕ) : ℕ := if k ≤ p then k else k - 1

/-- Lifted wire ↦ real wire. -/
def lowerWire (n p i : ℕ) : ℕ := realWire n p (i - (n + 1))

theorem lowerWire_liftIdx (n p k : ℕ) (hk : k ≠ p) : lowerWire n p (n + 1 + notSkipIdx p k) = n + k := by
  unfold lowerWire realWire notSkipIdx
  split_ifs <;> omega

variable (gates : List Gate) (p : ℕ) (hp : p < gates.length)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates) (hN : (gates[p]'hp).op = GateOp.not)

include hp in
theorem val_liftIdx (x : Fin n → Bool) (k : ℕ) (hk : k ≠ p) :
    val gates x (n + k) = val (lift n p gates) (nuPt gates p x) (n + 1 + notSkipIdx p k) := by
  rw [val_lift (n := n) gates p hp x (n + k)]
  congr 1
  unfold liftWire notSkipIdx
  split_ifs <;> omega

include hp in
/-- The lifted trace of real gate `k ≠ p` is the real trace through `castSucc`. -/
theorem trRT_lift (R : Finset (Fin n)) (z : Fin n → Bool) (k : ℕ) (hk : k ≠ p) :
    trRT (realAtoms gates p z) (liftSet R) (lift n p gates) (n + 1 + notSkipIdx p k) =
      (trRT (upPt z) R gates (n + k)).image Fin.castSucc := by
  ext c
  simp only [trRT, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hc, hv⟩
    obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    rw [realAtoms_castSucc, ← val_liftIdx gates p hp _ k hk] at hv
    exact ⟨u, ⟨hu, hv⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hv⟩, rfl⟩
    refine ⟨mem_liftSet_iff.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [realAtoms_castSucc, ← val_liftIdx gates p hp _ k hk]
    exact hv

include hp hg hU hN in
/-- **The real run and the lifted run agree** (labels through `castSucc`, merges through
`lowerWire`). -/
theorem run_lift (R : Finset (Fin n)) (z : Fin n → Bool) : ∀ k ≤ gates.length,
    (∀ u ∈ R, Fin.castSucc (runLT z (upPt z) R gates k u) =
      runLT (nuPt gates p z) (realAtoms gates p z) (liftSet R) (lift n p gates) (notSkipCnt p k)
        (Fin.castSucc u)) ∧
    runMT z (upPt z) R gates k =
      (runMT (nuPt gates p z) (realAtoms gates p z) (liftSet R) (lift n p gates) (notSkipCnt p k)).image
        (lowerWire n p) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun u _ => ?_, ?_⟩
    · simp [notSkipCnt, runLT]
    · simp [notSkipCnt, runMT]
  | succ k ih =>
    intro hk
    obtain ⟨hL, hM⟩ := ih (by omega)
    set l := runLT z (upPt z) R gates k with hl
    by_cases hkp : k = p
    · -- the NOT gate never merges
      subst hkp
      have hnm : ¬ MgT z (upPt z) R gates l k := by
        rintro ⟨hz, hc⟩
        have hempty : trRT (upPt z) R gates (n + k) = ∅ := by
          refine Finset.filter_false_of_mem fun u _ hu => ?_
          have := not_false_of_le gates k hp hg hU hN (le_upPt z u) hz
          rw [this] at hu
          exact absurd hu (by decide)
        rw [hempty, Finset.image_empty, Finset.card_empty] at hc
        omega
      have hc : notSkipCnt k (k + 1) = notSkipCnt k k := by unfold notSkipCnt; split_ifs <;> omega
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [runLT_succ, mstepT_nomerge z (upPt z) R gates hnm, hc]
        exact hL u hu
      · rw [runMT, ite_eq_right hnm, hc]
        exact hM
    · set j := notSkipIdx p k with hj
      have hc0 : notSkipCnt p k = j := by rw [hj]; unfold notSkipCnt notSkipIdx; split_ifs <;> omega
      have hc1 : notSkipCnt p (k + 1) = j + 1 := by rw [hj]; unfold notSkipCnt notSkipIdx; split_ifs <;> omega
      rw [hc0] at hL hM
      rw [hc1]
      set l' := runLT (nuPt gates p z) (realAtoms gates p z) (liftSet R) (lift n p gates) j with hl'
      have hT' : trRT (realAtoms gates p z) (liftSet R) (lift n p gates) (n + 1 + j) =
          (trRT (upPt z) R gates (n + k)).image Fin.castSucc := trRT_lift gates p hp R z k hkp
      have hTR : trRT (upPt z) R gates (n + k) ⊆ R := Finset.filter_subset _ _
      have himg : (trRT (realAtoms gates p z) (liftSet R) (lift n p gates) (n + 1 + j)).image l' =
          ((trRT (upPt z) R gates (n + k)).image l).image Fin.castSucc := by
        rw [hT', Finset.image_image, Finset.image_image]
        exact Finset.image_congr fun u hu => (hL u (hTR hu)).symm
      have hval : val gates z (n + k) = val (lift n p gates) (nuPt gates p z) (n + 1 + j) :=
        val_liftIdx gates p hp z k hkp
      have hmg : MgT z (upPt z) R gates l k ↔
          MgT (nuPt gates p z) (realAtoms gates p z) (liftSet R) (lift n p gates) l' j := by
        unfold MgT
        rw [← hval, show n + 1 + j = (n + 1) + j from rfl, himg,
          Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
      by_cases hm : MgT z (upPt z) R gates l k
      · have hm' := hmg.mp hm
        refine ⟨fun u hu => ?_, ?_⟩
        · rw [runLT_succ, runLT_succ, mstepT_apply z (upPt z) R gates hm,
            mstepT_apply _ _ _ _ hm', ← hL u hu]
          simp only [himg]
          by_cases hin : l u ∈ (trRT (upPt z) R gates (n + k)).image l
          · rw [ite_eq_left hin, ite_eq_left (Finset.mem_image_of_mem _ hin), mrep, mrep,
              Finset.min'_image Fin.strictMono_castSucc.monotone]
          · have hin' : Fin.castSucc (l u) ∉ ((trRT (upPt z) R gates (n + k)).image l).image
                Fin.castSucc := fun h =>
              hin ((Fin.castSucc_injective n).mem_finset_image.mp h)
            rw [ite_eq_right hin, ite_eq_right hin']
        · rw [runMT, ite_eq_left hm, runMT, ite_eq_left hm', hM,
            Finset.image_insert, show n + 1 + j = (n + 1) + j from rfl, lowerWire_liftIdx n p k hkp]
      · have hm' : ¬ MgT (nuPt gates p z) (realAtoms gates p z) (liftSet R) (lift n p gates) l' j :=
          fun h => hm (hmg.mpr h)
        refine ⟨fun u hu => ?_, ?_⟩
        · rw [runLT_succ, runLT_succ, mstepT_nomerge z (upPt z) R gates hm, mstepT_nomerge _ _ _ _ hm']
          exact hL u hu
        · rw [runMT, ite_eq_right hm, runMT, ite_eq_right hm']
          exact hM

include hp hg hU hN in
/-- **L-LIFT**: the real merge set is the class of the lifted real test system, in real wires. -/
theorem mergeSet_eq_lift (R : Finset (Fin n)) (z : Fin n → Bool) :
    mergeSet gates R z = (ltsCls gates p R (realLTS gates p z)).image (lowerWire n p) := by
  have h := (run_lift gates p hp hg hU hN R z gates.length le_rfl).2
  have hc : notSkipCnt p gates.length = (lift n p gates).length := by
    rw [length_lift n p gates hp]; unfold notSkipCnt; split_ifs <;> omega
  rw [hc] at h
  exact h

include hp hg hU hN in
/-- **The lifted real test system is valid** at a zero point of `R` (`o` computes `OR_R`). -/
theorem realLTS_valid (R : Finset (Fin n)) (o : ℕ)
    (hev : ∀ x : Fin n → Bool, val gates x o = decide (∃ v ∈ R, x v = true))
    (z : Fin n → Bool) (hz : ∀ v ∈ R, z v = false) : LTSValid gates p R o (realLTS gates p z) := by
  refine ⟨?_, fun c hc => ?_, fun x hx c hc c' hc' h1 h2 => ?_⟩
  · show val (lift n p gates) (nuPt gates p z) (liftWire n p o) = false
    rw [nuPt, ← val_lift (n := n) gates p hp z o, hev]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hzv
    rw [hz v hv] at hzv
    exact absurd hzv (by decide)
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    show val (lift n p gates) (realAtoms gates p z (Fin.castSucc u)) (liftWire n p o) = true
    rw [realAtoms_castSucc, nuPt, ← val_lift (n := n) gates p hp _ o, hev]
    exact decide_eq_true ⟨u, hu, by simp [upPt]⟩
  · obtain ⟨u, hu, rfl⟩ := mem_liftSet_iff.mp hc
    obtain ⟨v, hv, rfl⟩ := mem_liftSet_iff.mp hc'
    change nuPt gates p z x = false at hx
    change realAtoms gates p z (Fin.castSucc u) x = true at h1
    change realAtoms gates p z (Fin.castSucc v) x = true at h2
    rw [realAtoms_castSucc] at h1 h2
    induction x using Fin.lastCases with
    | last =>
      rw [nuPt, ext_last] at hx h1
      rw [not_false_of_le gates p hp hg hU hN (le_upPt z u) hx] at h1
      exact absurd h1 (by decide)
    | cast y =>
      rw [nuPt, ext_castSucc] at hx h1 h2
      rw [← upPt_hT z u y h1 hx, ← upPt_hT z v y h2 hx]

include hp hg hU hN in
/-- **MergeSDR ⇒ LiftSDR.** -/
theorem liftSDR_of_mergeSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : MergeSDR S gates) : LiftSDR S gates out p := by
  obtain ⟨z, hz, hdis⟩ := H
  refine ⟨fun w => realLTS gates p (z w), fun w => realLTS_valid gates p hp hg hU hN (S w) (out w) (hev w)
    (z w) (hz w), fun w w' hww => Finset.disjoint_left.mpr fun g hgw hgw' => ?_⟩
  have h := hdis w w' hww
  rw [mergeSet_eq_lift gates p hp hg hU hN, mergeSet_eq_lift gates p hp hg hU hN] at h
  exact Finset.disjoint_left.mp h (Finset.mem_image_of_mem _ hgw) (Finset.mem_image_of_mem _ hgw')

include hp hg hU hN in
/-- **MergeSDR ⇒ MUL.** -/
theorem muL_of_mergeSDR {m : ℕ} (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (H : MergeSDR S gates) : MUL S gates out p :=
  mu_of_liftSDR gates p hp hg hU hN S out (liftSDR_of_mergeSDR gates p hp hg hU hN S out hev H)

end LLift

end PEqualNP.Outside.L_meta_951_aux
