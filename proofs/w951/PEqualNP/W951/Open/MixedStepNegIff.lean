import PEqualNP.W951.Open.MixedSlack

/-!
# MixedStepNegIff: the mixed step at negative states IS the count at every mixed state (seat A1)

Board `open-one-not`, seat A1. Note: `research/one-not/research/open/A1_mixed_step.md`.

The missing arrow `MixedSlack.MixedStepNeg` asks for a non-increasing 0-step or 1-step at every mixed
state of NEGATIVE slack. This file shows that, for one gate list, this local-looking hypothesis is
equivalent to the global count `0 ≤ mslack` at EVERY mixed state, so a step lemma that is used only at
negative states carries no local content: proving it means proving the count at all restrictions.

* `stepNeg_iff_nonneg`: for one gate list, "a non-increasing step at every negative mixed state"
  ↔ "the mixed slack is nonnegative at every mixed state" (max principle one way, vacuity the other).
* `mixedStepNeg_iff`: `MixedStepNeg` ↔ every minimal counterexample has `0 ≤ mslack` at every mixed state.
* `abstract_descent_iff`: the hypothesis of `Continuous.no_minCE_of_mixed_descent` with an ABSTRACT `f`
  (only `f ∅ ∅ = slack ∅` pinned) is equivalent to `0 ≤ slack ∅` itself: the abstract form is the bare count.
-/

namespace PEqualNP.Outside.L_meta_951_aux.MixedSlack

open Finset
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_951_aux

variable {n m : ℕ}

/-- The step at negative states, for one gate list. -/
def StepNeg (gates : List Gate) (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ Q D : Finset (Fin n), Disjoint Q D → mslack gates S Q D < 0 →
    ∃ v : Fin n, v ∉ Q ∪ D ∧
      (mslack gates S (insert v Q) D ≤ mslack gates S Q D ∨
       mslack gates S Q (insert v D) ≤ mslack gates S Q D)

/-- The count at every mixed state, for one gate list. -/
def MixedCount (gates : List Gate) (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ Q D : Finset (Fin n), Disjoint Q D → 0 ≤ mslack gates S Q D

/-- **The step at the negative states is the count at all states.** -/
theorem stepNeg_iff_nonneg (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    StepNeg gates S ↔ MixedCount gates S := by
  classical
  constructor
  · intro H
    let f : Finset (Fin n) × Finset (Fin n) → ℤ :=
      fun s => if Disjoint s.1 s.2 then mslack gates S s.1 s.2 else 0
    have key := Continuous.nonneg_of_descent_at_neg
      (fun s : Finset (Fin n) × Finset (Fin n) => n - (s.1 ∪ s.2).card) f (by
        rintro ⟨Q, D⟩ hneg
        simp only [f] at hneg
        by_cases hd : Disjoint Q D
        · rw [if_pos hd] at hneg
          obtain ⟨v, hv, h⟩ := H Q D hd hneg
          have hvQ : v ∉ Q := fun h' => hv (mem_union_left _ h')
          have hvD : v ∉ D := fun h' => hv (mem_union_right _ h')
          have hn : ∀ T : Finset (Fin n), T.card ≤ n := fun T => by
            simpa using Finset.card_le_univ T
          rcases h with h | h
          · refine ⟨(insert v Q, D), ?_, ?_⟩
            · have hc : (Q ∪ D).card < (insert v Q ∪ D).card := by
                rw [insert_union]; exact Finset.card_lt_card (ssubset_insert hv)
              have := hn (insert v Q ∪ D)
              show n - (insert v Q ∪ D).card < n - (Q ∪ D).card
              omega
            · have hd' : Disjoint (insert v Q) D := disjoint_insert_left.mpr ⟨hvD, hd⟩
              simp only [f, if_pos hd', if_pos hd]; exact h
          · refine ⟨(Q, insert v D), ?_, ?_⟩
            · have hc : (Q ∪ D).card < (Q ∪ insert v D).card := by
                rw [union_insert]; exact Finset.card_lt_card (ssubset_insert hv)
              have := hn (Q ∪ insert v D)
              show n - (Q ∪ insert v D).card < n - (Q ∪ D).card
              omega
            · have hd' : Disjoint Q (insert v D) := disjoint_insert_right.mpr ⟨hvQ, hd⟩
              simp only [f, if_pos hd', if_pos hd]; exact h
        · rw [if_neg hd] at hneg
          exact absurd hneg (lt_irrefl _))
    intro Q D hd
    have := key (Q, D)
    simpa [f, if_pos hd] using this
  · intro H Q D hd hneg
    exact absurd (H Q D hd) (not_le.mpr hneg)

/-- **`MixedStepNeg` is the count at every mixed state of every minimal counterexample.** -/
theorem mixedStepNeg_iff :
    MixedStepNeg ↔ ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ),
      MinCE S gates out → MixedCount gates S := by
  constructor
  · intro H n m S gates out M
    exact (stepNeg_iff_nonneg gates S).mp (fun Q D hd hneg => H n m S gates out M Q D hd hneg)
  · intro H n m S gates out M Q D hd hneg
    exact (stepNeg_iff_nonneg gates S).mpr (H n m S gates out M) Q D hd hneg

/-- **The abstract descent hypothesis is the bare count.** With only `f ∅ ∅ = slack ∅` pinned, the
hypothesis of `Continuous.no_minCE_of_mixed_descent` holds iff `0 ≤ slack gates S ∅`. -/
theorem abstract_descent_iff (gates : List Gate) (S : Fin m → Finset (Fin n)) :
    (∃ f : Finset (Fin n) → Finset (Fin n) → ℤ, f ∅ ∅ = slack gates S ∅ ∧
      ∀ Q R, f Q R < 0 → ∃ Q' R', Q ∪ R ⊂ Q' ∪ R' ∧ f Q' R' ≤ f Q R) ↔
    0 ≤ slack gates S ∅ := by
  constructor
  · rintro ⟨f, h0, hstep⟩
    have key := Continuous.nonneg_of_descent_at_neg
      (fun s : Finset (Fin n) × Finset (Fin n) => n - (s.1 ∪ s.2).card) (fun s => f s.1 s.2) (by
        rintro ⟨Q, R⟩ hQ
        obtain ⟨Q', R', hlt, hle⟩ := hstep Q R hQ
        refine ⟨(Q', R'), ?_, hle⟩
        have hc : (Q ∪ R).card < (Q' ∪ R').card := Finset.card_lt_card hlt
        have hn : (Q' ∪ R').card ≤ n := by simpa using Finset.card_le_univ (Q' ∪ R')
        show n - (Q' ∪ R').card < n - (Q ∪ R).card
        omega) (∅, ∅)
    rw [← h0]; exact key
  · intro h
    exact ⟨fun _ _ => slack gates S ∅, rfl, fun Q R hneg => absurd h (not_le.mpr hneg)⟩

end PEqualNP.Outside.L_meta_951_aux.MixedSlack
