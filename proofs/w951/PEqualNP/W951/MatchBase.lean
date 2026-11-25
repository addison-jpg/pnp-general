import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.FracMatch
import PEqualNP.W951.HardFrac

/-! W951's matching layer on the circuit-free base (`PEqualNP.Base.Matching`).

* `TestSys.cnt_subset`, `card_biUnion_le_length` (in `FracMatch.lean`): counted wires are gate
  wires, so any union of counted sets has at most `gates.length` elements.
* `matchG_iff_hall`, `matchG_iff_exists_hall`: `MatchG` is Hall's condition on the counted sets.
* `bound_of_matchG'`: the MatchG bound as a corollary of the base; `bound_of_fracMatch'` is an
  alias of `bound_of_fracMatch`, which `FracMatch.lean` proves from the base.

The bridge `hardCase_of_fracMatch` already exists in `HardFrac.lean`; nothing is added for it. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- For a fixed choice of test systems, the `MatchG` injection exists exactly when Hall's
inequality holds for the counted sets. -/
theorem matchG_iff_hall {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    {out : Fin m → ℕ} (σ : ∀ w, TestSys n gates (S w) (out w)) :
    (∃ f : (Σ w : Fin m, Fin ((S w).card - 1)) → ℕ, Function.Injective f ∧
        ∀ x, f x ∈ (σ x.1).cnt) ↔
      ∀ s : Finset (Fin m),
        ∑ w ∈ s, ((S w).card - 1) ≤ (s.biUnion fun w => (σ w).cnt).card := by
  rw [← hasBMatching_one_iff (fun w => (σ w).cnt) (fun w => (S w).card - 1), hasBMatching_iff]
  simp

/-- `MatchG` is Hall's condition for some choice of test systems. -/
theorem matchG_iff_exists_hall {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) :
    MatchG S gates out ↔ ∃ σ : ∀ w, TestSys n gates (S w) (out w), ∀ s : Finset (Fin m),
      ∑ w ∈ s, ((S w).card - 1) ≤ (s.biUnion fun w => (σ w).cnt).card :=
  exists_congr fun σ => matchG_iff_hall S σ

/-- `bound_of_matchG` from the base: Hall's inequality at `s = univ`. -/
theorem bound_of_matchG' {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hg : MatchG S gates out) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  obtain ⟨σ, h⟩ := (matchG_iff_exists_hall S gates out).1 hg
  exact (h Finset.univ).trans (card_biUnion_le_length _ _ fun w _ => (σ w).cnt_subset)

/-- `bound_of_fracMatch` (proved from the base in `FracMatch.lean`). -/
alias bound_of_fracMatch' := bound_of_fracMatch

end PEqualNP.Outside.L_meta_951_aux
