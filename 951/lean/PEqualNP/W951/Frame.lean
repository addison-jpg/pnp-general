import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Count

/-! Counting with general test systems (front's piece of the W951 split).
A zero point `z` and test points `p u` with `p u` false wherever `z` is false, except at `u`
(hypothesis `hT`). `main_invT` / `countT_bound` generalize `main_inv` from unit test points
`eof u` to arbitrary `p u` (Lemma G / Frame Lemma). The generic definitions (`GoodT`..`DT`) and
the union-find run proving the invariant live in `MergeRunT.lean`; `main_invT` (its corollary) and
`main_inv` are in `Count.lean`. -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-! ## Counting with general test systems (zero point `z`, test points `p u`) -/

/-- Lemma G: a set whose output is false at `z` and true at every test point needs at least
`|S| - 1` counted wires. -/
theorem countT_bound {n : ℕ} (z : Fin n → Bool) (p : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hT : ∀ u ∈ S, ∀ c : Fin n, p u c = true → z c = false → c = u)
    (gs : List Gate) (hgood : GoodT z p S gs) (o : ℕ)
    (hz : val gs z o = false) (hp : ∀ u ∈ S, val gs (p u) o = true) :
    S.card - 1 ≤ (DT z p S gs).card := by
  obtain ⟨l, hinv, hcard⟩ := main_invT z p S hT gs hgood
  have h1 : (S.image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact hinv o u v hz (hp u hu) (hp v hv) hu hv
  omega

end PEqualNP.Outside.L_meta_951_aux
