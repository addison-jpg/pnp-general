import Mathlib
import PEqualNP.Defs
import PEqualNP.Base.Matching.Hall
import PEqualNP.W951.MatchG

/-! Fractional version of the matching charge (weaker than MatchG, same bound).

Each set `w` mixes over finitely many test systems `σ w j` (`j < k w`) with weights `lam w j ≥ 0`
summing to `1`. For each system it names a set `M w j` of at least `|S w| - 1` counted wires.
The load of a wire `g` is `∑ w, ∑ j, lam w j * [g ∈ M w j]`. If every load is at most `1`,
then `∑ w, (|S w| - 1) ≤ #gates`: each set receives at least its demand, each wire gives out at
most one unit. With one system per set and weight `1` this is exactly MatchG; mixing over zero
points is what makes it weaker (bipartite matching alone is integral).

The three facts are corollaries of the circuit-free base (`PEqualNP.Base.Matching`):
`bound_of_fracMatch` of `sum_le_card_of_frac`, `fracMatch_of_matchG` of
`image_props_of_injective_one` (capacity `1`), `fracMatch_of_matchG2` of
`image_props_of_injective_sigmaProd` (capacity `2`). The only circuit fact is
`TestSys.cnt_subset`: counted wires are gate wires. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Base.Matching

/-- FracMatch: weighted mixtures of test systems whose wire loads are at most one. -/
def FracMatch {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ (k : Fin m → ℕ) (σ : ∀ w, Fin (k w) → TestSys n gates (S w) (out w))
    (lam : ∀ w, Fin (k w) → ℝ) (M : ∀ w, Fin (k w) → Finset ℕ),
    (∀ w j, 0 ≤ lam w j) ∧ (∀ w, ∑ j, lam w j = 1) ∧
    (∀ w j, M w j ⊆ (σ w j).cnt) ∧ (∀ w j, (S w).card - 1 ≤ (M w j).card) ∧
    ∀ g : ℕ, ∑ w, ∑ j, (if g ∈ M w j then lam w j else 0) ≤ 1

/-- Counted wires are gate wires. -/
theorem TestSys.cnt_subset {n : ℕ} {gates : List Gate} {S : Finset (Fin n)} {o : ℕ}
    (σ : TestSys n gates S o) : σ.cnt ⊆ Finset.Ico n (n + gates.length) := by
  intro i hi
  simp only [TestSys.cnt, DT, Finset.mem_filter, mask_length] at hi
  exact hi.1

/-- A union of sets of gate wires has at most `gates.length` elements. -/
theorem card_biUnion_le_length {κ : Type*} {n : ℕ} {gates : List Gate} (s : Finset κ)
    (M : κ → Finset ℕ) (hM : ∀ j ∈ s, M j ⊆ Finset.Ico n (n + gates.length)) :
    (s.biUnion M).card ≤ gates.length := by
  simpa using Finset.card_le_card (Finset.biUnion_subset.2 hM)

/-- FracMatch gives the bound (`sum_le_card_of_frac`). -/
theorem bound_of_fracMatch {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hf : FracMatch S gates out) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  obtain ⟨k, σ, lam, M, hlam0, hlam1, hMsub, hMcard, hload⟩ := hf
  exact (sum_le_card_of_frac Finset.univ k lam M _ hlam0 (fun w _ => hlam1 w) hMcard hload).trans
    (card_biUnion_le_length _ _ fun x _ => (hMsub x.1 x.2).trans (σ x.1 x.2).cnt_subset)

/-- MatchG implies FracMatch (one system per set, weight one, `M` = the matched wires;
`image_props_of_injective_one`, capacity one). -/
theorem fracMatch_of_matchG {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hg : MatchG S gates out) : FracMatch S gates out := by
  classical
  obtain ⟨σ, f, hinj, hmem⟩ := hg
  obtain ⟨hsub, hcard, hload⟩ := image_props_of_injective_one (K := ℝ)
    (t := fun w => (σ w).cnt) f hinj hmem
  exact ⟨fun _ => 1, fun w _ => σ w, fun _ _ => 1, fun w _ => _, fun _ _ => zero_le_one,
    fun w => by simp, fun w _ => hsub w, fun w _ => (hcard w).ge,
    fun g => by simpa using hload Finset.univ g⟩

/-- Two-world matching: every set has two test systems (index `c : Fin 2`, e.g. canonical / R*),
each slot `(w, c, k)`, `k < |S w| - 1`, gets a counted wire of system `c` of `w` together with a copy
index in `Fin 2` (each wire has capacity two), injectively; within one system the wires are distinct.
By Hall's theorem this is the "two-world Hall" condition. -/
def MatchG2 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ) :
    Prop :=
  ∃ σ : ∀ w, Fin 2 → TestSys n gates (S w) (out w),
    ∃ f : (Σ _w : Fin m, Fin 2 × Fin ((S _w).card - 1)) → ℕ × Fin 2, Function.Injective f ∧
      (∀ x, (f x).1 ∈ (σ x.1 x.2.1).cnt) ∧
      ∀ w c, Function.Injective fun k : Fin ((S w).card - 1) => (f ⟨w, (c, k)⟩).1

/-- Two-world matching gives FracMatch (weight 1/2 on each system;
`image_props_of_injective_sigmaProd`, capacity two). -/
theorem fracMatch_of_matchG2 {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (hg : MatchG2 S gates out) : FracMatch S gates out := by
  classical
  obtain ⟨σ, f, hinj, hmem, hloc⟩ := hg
  obtain ⟨hsub, hcard, hload⟩ := image_props_of_injective_sigmaProd (K := ℝ)
    (t := fun w c => (σ w c).cnt) f hinj hmem hloc
  exact ⟨fun _ => 2, σ, fun _ _ => 1 / (2 : ℕ), _, fun _ _ => by norm_num, fun w => by simp,
    hsub, fun w c => (hcard w c).ge, hload Finset.univ⟩

end PEqualNP.Outside.L_meta_951_aux
