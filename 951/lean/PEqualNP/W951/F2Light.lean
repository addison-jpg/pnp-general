import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.F2SeeK3

/-!
# F2Light: research's light-case lemmas B and K0-K3 (refereed CORRECT, dwV8p), LIGHT-STAR ⇒ the step

`951/board/agents/research-F2-light.md` §2-§4 and the referee note `dwV8p-referee-F2-light.md`. A
light instance: `h(Q + e_u) = 0` (the NOT gate is `1`) at every alive point `u`.

* **B** (the bottom system): for an alive set `w`, the real union-find run at zero point `Q`, atoms
  `Q + e_u`, has at least `d_w` merges (`bottom_card`), all in `F2(Q)` (`bottom_subset_F2`). Neither needs
  lightness; with it the run lies in `{h = 0}`, where the real circuit is `C_1` (`real_eq_C1_of_not`).
* **K0** (`K0_not_mem`): `C_0(g)(Q + e_v) = 1` ⇒ `g ∉ F2(Q ∪ {v})` (from `not_F2Wit_of_C0`).
* **K1** (`K1_world0`): `C_1(g)(Q + e_v) = 1` ⇒ every point `Z' ⊇ Q ∪ {v}` avoiding a set `R'` with
  `g(Z') = 0` has `h(Z') = 1` and `h(top_R') = 1`: world-0 witnesses of type-A sets only.
* **K2** (`K2_world0`): `real g(Q + e_v) = 1` gives `C_1(g)(Q + e_v) = 1`, so K1 applies (a bottom merge whose
  block contains `v`).
* **K3**: `K3` and `seeK3_subset_gain` (F2SeeK3).
* **LIGHT-STAR** (repaired wording, 12:55; OPEN, as a hypothesis): `LightStar` (`cost(v) ≤ |(bottom merges of
  star(v) ∪ K0Set(v)) \ F2(Q ∪ {v})|`) ⇒ `GainF2` (`gainF2_of_lightStar`).
-/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

section F2Light

variable {n m : ℕ} (gates : List Gate)
  (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2)
  (hU : AtMostOneNot gates)

theorem canonPt_zero_of_alive {S : Fin m → Finset (Fin n)} {Q : Finset (Fin n)} {w : Fin m}
    (hw : w ∈ aliveSets S Q) : ∀ x ∈ S w, canonPt Q x = false := by
  intro x hx
  simp only [canonPt, decide_eq_false_iff_not]
  exact Finset.disjoint_left.mp (mem_aliveSets.mp hw) hx

include hg hU in
/-- **B, count**: the bottom system of an alive set has at least `d_w` merges. -/
theorem bottom_card (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (Q : Finset (Fin n)) {w : Fin m} (hw : w ∈ aliveSets S Q) :
    (S w).card - 1 ≤ (mergeSet gates (S w) (canonPt Q)).card := by
  refine mergeSet_card_ge gates hg hU (S w) (canonPt Q) (out w) ?_ fun u hu => ?_
  · rw [hev]
    simpa using fun y hy => canonPt_zero_of_alive hw y hy
  · rw [hev]
    exact decide_eq_true ⟨u, hu, by simp [upPt]⟩

include hg hU in
/-- **B, membership**: the bottom merges of an alive set lie in `F2(Q)` (witness at `Z = Q`). -/
theorem bottom_subset_F2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) {w : Fin m}
    (hw : w ∈ aliveSets S Q) : mergeSet gates (S w) (canonPt Q) ⊆ F2 gates S Q :=
  mergeSet_subset_F2 gates hg hU S Q hw (canonPt Q) (canonPt_zero_of_alive hw)
    fun _ hx => canonPt_eq_true.mpr hx

/-- Where the NOT gate is `1` (`h = 0`), the real circuit is `C_1`. -/
theorem real_eq_C1_of_not (p : ℕ) (hp : p < gates.length) (x : Fin n → Bool)
    (hx : val gates x (n + p) = true) (i : ℕ) :
    val gates x i = val (lift n p gates) (ext x true) (liftWire n p i) := by
  have e := val_lift (n := n) gates p hp x i
  rwa [hx] at e

/-- **The bottom pool of `v`**: the bottom merges of the sets through `v`. -/
noncomputable def bottomPool (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Finset ℕ :=
  (starSets S Q v).biUnion fun w => mergeSet gates (S w) (canonPt Q)

include hg hU in
theorem bottomPool_subset_F2 (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    bottomPool gates S Q v ⊆ F2 gates S Q :=
  Finset.biUnion_subset.mpr fun _ hw =>
    bottom_subset_F2 gates hg hU S Q (Finset.mem_filter.mp hw).1

open Classical in
/-- `K0(v)` (`K0Set`): the `F2(Q)` gates with `C_0(g)(Q + e_v) = 1`. -/
noncomputable def K0Set (p : ℕ) (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) :
    Finset ℕ :=
  (F2 gates S Q).filter fun i =>
    val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true

variable (p : ℕ) (hp : p < gates.length) (hN : (gates[p]'hp).op = GateOp.not)

include hg hU hN in
/-- **K0**: `C_0(g)(Q + e_v) = 1` kills `g`. -/
theorem K0_not_mem (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) {i : ℕ}
    (h0 : val (lift n p gates) (ext (canonPt (insert v Q)) false) (liftWire n p i) = true) :
    i ∉ F2 gates S (insert v Q) := fun hi => by
  obtain ⟨-, w, -, hwit⟩ := mem_F2.mp hi
  exact not_F2Wit_of_C0 gates p hp hg hU hN (S w) (insert v Q) h0 hwit

include hg hU hN in
/-- **K1**: `C_1(g)(Q + e_v) = 1` ⇒ every zero point `Z' ⊇ Q ∪ {v}` of `g` avoiding a set `R'` has
`h(Z') = 1` and `h(top_R') = 1` (world 0; `R'` type A at `Q ∪ {v}`). -/
theorem K1_world0 (Q : Finset (Fin n)) (v : Fin n) {i : ℕ}
    (hC1 : val (lift n p gates) (ext (canonPt (insert v Q)) true) (liftWire n p i) = true)
    (R' : Finset (Fin n)) (Z' : Fin n → Bool) (hZR : ∀ x ∈ R', Z' x = false)
    (hZQ : ∀ x ∈ insert v Q, Z' x = true) (hz : val gates Z' i = false) :
    val gates Z' (n + p) = false ∧ val gates (Zof R') (n + p) = false := by
  have hm := monoList_lift (n := n) gates p hp hg hU hN
  have hle : canonPt (insert v Q) ≤ Z' := canonPt_le fun c hc => hZQ c hc
  have hNZ : val gates Z' (n + p) = false := by
    cases hN' : val gates Z' (n + p) with
    | false => rfl
    | true =>
      have e := real_eq_C1_of_not gates p hp Z' hN' i
      have hmono := val_le_of_le (lift n p gates) hm.andOr (ext_le_of_le hle (le_refl true))
        (liftWire n p i)
      rw [hC1, ← e, hz] at hmono
      exact absurd hmono (by decide)
  refine ⟨hNZ, not_false_of_le gates p hp hg hU hN (fun c => ?_) hNZ⟩
  refine Bool.le_iff_imp.mpr fun hc => ?_
  have hcR : c ∉ R' := fun h => by rw [hZR c h] at hc; exact absurd hc (by decide)
  simp [Zof, hcR]

include hg hU hN in
/-- **K2**: a gate that is `1` at `Q + e_v` in the real circuit has `C_1 = 1` there, so K1 applies. -/
theorem K2_world0 (Q : Finset (Fin n)) (v : Fin n) {i : ℕ}
    (hreal : val gates (canonPt (insert v Q)) i = true) (R' : Finset (Fin n)) (Z' : Fin n → Bool)
    (hZR : ∀ x ∈ R', Z' x = false) (hZQ : ∀ x ∈ insert v Q, Z' x = true)
    (hz : val gates Z' i = false) :
    val gates Z' (n + p) = false ∧ val gates (Zof R') (n + p) = false :=
  K1_world0 gates hg hU p hp hN Q v ((lift_exact (n := n) gates p hp hg hU hN _ i).2.1 hreal)
    R' Z' hZR hZQ hz

/-- **LIGHT-STAR(v)** (research §4, repaired wording; OPEN): `cost(v)` gates of the bottom pool of `v`
and of `K0Set(v)` have no witness at `Q ∪ {v}`. -/
def LightStar (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n) : Prop :=
  ∑ w ∈ starSets S Q v, ((S w).card - 1) ≤
    ((bottomPool gates S Q v ∪ K0Set gates p S Q v) \ F2 gates S (insert v Q)).card

include hg hU in
/-- **LIGHT-STAR ⇒ the F2 step.** -/
theorem gainF2_of_lightStar (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) (v : Fin n)
    (H : LightStar gates p S Q v) : GainF2 gates S Q v := by
  classical
  refine H.trans (Finset.card_le_card fun i hi => ?_)
  obtain ⟨hi, hout⟩ := Finset.mem_sdiff.mp hi
  refine Finset.mem_sdiff.mpr ⟨?_, hout⟩
  rcases Finset.mem_union.mp hi with h | h
  · exact bottomPool_subset_F2 gates hg hU S Q v h
  · exact (Finset.mem_filter.mp h).1

end F2Light

end PEqualNP.Outside.L_meta_951_aux
