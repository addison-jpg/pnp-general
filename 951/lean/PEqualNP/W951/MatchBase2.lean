import PEqualNP.Base.Matching.Simple
import PEqualNP.W951.MatchBase

/-! W951's two-world matching (`MatchG2`) on the circuit-free base.

* `matchG2_iff_simpleBMatching`, `matchG2_iff_simpleHall`, `matchG2_iff_exists_simpleHall`:
  for fixed test systems, the `MatchG2` injection is a simple b-matching of the vertices
  `(w, c) : Fin m × Fin 2` (demand `|S w| - 1`) into gate wires of capacity two, hence equivalent
  to the simple Hall inequality.
* `fracMatch_of_matchG'`, `fracMatch_of_matchG2'`: aliases of the two `FracMatch` lemmas, which
  `FracMatch.lean` proves from `image_props_of_injective_one` / `image_props_of_injective_sigmaProd`
  (capacity `1`, `2`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- For fixed test systems, the `MatchG2` injection is a simple b-matching with capacity two. -/
theorem matchG2_iff_simpleBMatching {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    {out : Fin m → ℕ} (σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w)) :
    (∃ f : (Σ w : Fin m, Fin 2 × Fin ((S w).card - 1)) → ℕ × Fin 2, Function.Injective f ∧
        (∀ x, (f x).1 ∈ (σ x.1 x.2.1).cnt) ∧
        ∀ w c, Function.Injective fun k : Fin ((S w).card - 1) => (f ⟨w, (c, k)⟩).1) ↔
      HasSimpleBMatching (fun i : Fin m × Fin 2 => (σ i.1 i.2).cnt)
        (fun i => (S i.1).card - 1) (fun _ => 2) := by
  exact (hasSimpleBMatching_sigmaProd_iff (fun w c => (σ w c).cnt) _ 2).symm

/-- For fixed test systems, the `MatchG2` injection exists exactly when the simple Hall
inequality (gate capacity two) holds over the vertices `(w, c)`. -/
theorem matchG2_iff_simpleHall {n m : ℕ} (S : Fin m → Finset (Fin n)) {gates : List Gate}
    {out : Fin m → ℕ} (σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w)) :
    (∃ f : (Σ w : Fin m, Fin 2 × Fin ((S w).card - 1)) → ℕ × Fin 2, Function.Injective f ∧
        (∀ x, (f x).1 ∈ (σ x.1 x.2.1).cnt) ∧
        ∀ w c, Function.Injective fun k : Fin ((S w).card - 1) => (f ⟨w, (c, k)⟩).1) ↔
      ∀ s : Finset (Fin m × Fin 2), ∑ i ∈ s, ((S i.1).card - 1) ≤
        ∑ g ∈ s.biUnion (fun i => (σ i.1 i.2).cnt),
          min 2 (s.filter fun i => g ∈ (σ i.1 i.2).cnt).card :=
  exists_simple_injective_sigmaProd_iff_hall (fun w c => (σ w c).cnt) _ 2

/-- `MatchG2` is the simple Hall condition (capacity two) for some choice of test systems. -/
theorem matchG2_iff_exists_simpleHall {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) :
    MatchG2 S gates out ↔ ∃ σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w),
      ∀ s : Finset (Fin m × Fin 2), ∑ i ∈ s, ((S i.1).card - 1) ≤
        ∑ g ∈ s.biUnion (fun i => (σ i.1 i.2).cnt),
          min 2 (s.filter fun i => g ∈ (σ i.1 i.2).cnt).card :=
  exists_congr fun σ => matchG2_iff_simpleHall S σ

/-- `fracMatch_of_matchG` (proved from the base in `FracMatch.lean`). -/
alias fracMatch_of_matchG' := fracMatch_of_matchG

/-- `fracMatch_of_matchG2` (proved from the base in `FracMatch.lean`). -/
alias fracMatch_of_matchG2' := fracMatch_of_matchG2

end PEqualNP.Outside.L_meta_951_aux
