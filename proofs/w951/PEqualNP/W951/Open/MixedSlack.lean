import PEqualNP.W951.Continuous

/-!
# MixedSlack: mixed slack in the project's terms, and the missing arrow `MixedStepNeg`

A mixed state `(Q, D)` has the points of `Q` set to 1 and the points of `D` set to 0 (`Q`, `D` disjoint).

* `F2WitMix gates S Q D i`: wire `i` has a real witness for the set `S` at `(Q, D)`: an assignment `Z`
  with `Z = 1` on `Q`, `Z = 0` on `S ∪ D`, and two distinct points `u, u' ∈ S \ D` whose raising
  turns wire `i` from 0 to 1.
* `F2Mix gates S Q D`: the OR gates with such a witness for a set alive at `Q` (`S ∩ Q = ∅`).
* `mslack gates S Q D = |F2Mix| - baseDQ S D Q`.
* `mslack_empty`: at `(∅, ∅)` it is `slack gates S ∅`.
* `MixedStepNeg`: the missing arrow, a `Prop` (not proved). In every minimal counterexample, every
  state of negative mixed slack has a free point `v` whose 1-step or 0-step leaves the mixed slack no larger.
* `no_minCE_of_MixedStepNeg`: `MixedStepNeg → ∀ minimal counterexample, False`, i.e. `no_minCE`.
-/

namespace PEqualNP.Outside.L_meta_951_aux.MixedSlack

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

variable {n m : ℕ}

/-- the real witness of wire `i` for the set `R` at the mixed state `(Q, D)` -/
def F2WitMix (gates : List Gate) (R Q D : Finset (Fin n)) (i : ℕ) : Prop :=
  ∃ (Z : Fin n → Bool) (u u' : Fin n), u ∈ R \ D ∧ u' ∈ R \ D ∧ u ≠ u' ∧
    (∀ x ∈ R ∪ D, Z x = false) ∧ (∀ x ∈ Q, Z x = true) ∧ val gates Z i = false ∧
    val gates (Function.update Z u true) i = true ∧ val gates (Function.update Z u' true) i = true

open Classical in
/-- the OR gates with a real witness for a set alive at `Q`, at the mixed state `(Q, D)` -/
noncomputable def F2Mix (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) :
    Finset ℕ :=
  (Finset.Ico n (n + gates.length)).filter fun i =>
    IsOrAt gates (i - n) ∧ ∃ w ∈ aliveSets S Q, F2WitMix gates (S w) Q D i

/-- mixed slack: real-witness OR gates minus the base of the mixed state -/
noncomputable def mslack (gates : List Gate) (S : Fin m → Finset (Fin n)) (Q D : Finset (Fin n)) : ℤ :=
  ((F2Mix gates S Q D).card : ℤ) - (baseDQ S D Q : ℤ)

/-- at the empty state the mixed witness is the plain one -/
theorem F2WitMix_empty (gates : List Gate) (R : Finset (Fin n)) (i : ℕ) :
    F2WitMix gates R ∅ ∅ i ↔ F2Wit gates R ∅ i := by
  unfold F2WitMix F2Wit
  simp

open Classical in
theorem F2Mix_empty (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    F2Mix gates S ∅ ∅ = F2 gates S ∅ := by
  unfold F2Mix F2
  apply Finset.filter_congr
  intro i _
  simp only [F2WitMix_empty]

theorem mslack_empty (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    mslack gates S ∅ ∅ = slack gates S ∅ := by
  unfold mslack slack
  rw [F2Mix_empty]

/-- **The missing arrow** (a statement, not a theorem): in every minimal counterexample, a mixed state
of negative slack has a free point whose 1-step or 0-step leaves the mixed slack no larger. -/
def MixedStepNeg : Prop :=
  ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
    MinCE S gates out → ∀ Q D : Finset (Fin n), Disjoint Q D → mslack gates S Q D < 0 →
      ∃ v : Fin n, v ∉ Q ∪ D ∧
        (mslack gates S (insert v Q) D ≤ mslack gates S Q D ∨
         mslack gates S Q (insert v D) ≤ mslack gates S Q D)

/-- **The conditional**: the missing arrow closes `no_minCE`. -/
theorem no_minCE_of_MixedStepNeg (H : MixedStepNeg) :
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      ¬ MinCE S gates out := by
  classical
  refine Continuous.no_minCE_of_mixed_descent ?_
  intro n m S gates out M
  refine ⟨fun Q D => if Disjoint Q D then mslack gates S Q D else 0, by simp [mslack_empty], ?_⟩
  intro Q D hneg
  simp only at hneg ⊢
  by_cases hd : Disjoint Q D
  · rw [if_pos hd] at hneg ⊢
    obtain ⟨v, hv, h⟩ := H n m S gates out M Q D hd hneg
    have hvQ : v ∉ Q := fun h' => hv (mem_union_left _ h')
    have hvD : v ∉ D := fun h' => hv (mem_union_right _ h')
    rcases h with h | h
    · refine ⟨insert v Q, D, ?_, ?_⟩
      · rw [insert_union]
        exact ssubset_insert hv
      · have hd' : Disjoint (insert v Q) D := disjoint_insert_left.mpr ⟨hvD, hd⟩
        rw [if_pos hd']; exact h
    · refine ⟨Q, insert v D, ?_, ?_⟩
      · rw [union_insert]
        exact ssubset_insert hv
      · have hd' : Disjoint Q (insert v D) := disjoint_insert_right.mpr ⟨hvQ, hd⟩
        rw [if_pos hd']; exact h
  · rw [if_neg hd] at hneg
    exact absurd hneg (lt_irrefl _)

end PEqualNP.Outside.L_meta_951_aux.MixedSlack
