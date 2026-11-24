import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Final

-- Extension of the 951 base: the line-ORs of a projective plane of order q (step L-meta-952)
-- are a special case of 951 (lines meet in exactly one point, each line has q + 1 >= 3 points,
-- and the sum of (|line| - 1) over the m lines is m * q). So 952 holds as soon as 951 does:
-- this file adds no new sorry of its own.

namespace PEqualNP.Outside.L_meta_951_aux

theorem sum_const_sub {m q : ℕ} (S : Fin m → Finset (Fin m))
    (hcard : ∀ i : Fin m, (S i).card = q + 1) :
    ∑ i : Fin m, ((S i).card - 1) = m * q := by
  simp [hcard]

end PEqualNP.Outside.L_meta_951_aux

open PEqualNP.Outside.L_meta_951_aux in
theorem PEqualNP.Outside.L_meta_952 : ∀ (q m : ℕ) (S : Fin m → Finset (Fin m)), 2 ≤ q → m = q * q + q + 1 → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → (∀ p : Fin m, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card = q + 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin m → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → m * q ≤ gates.length := by
  intro q m S hq hm hcard hint _ gates out hg hι hev
  have h := PEqualNP.Outside.L_meta_951 m m S
    (fun i => by rw [hcard i]; omega) (fun i j hij => (hint i j hij).le) gates out hg hι hev
  rw [sum_const_sub S hcard] at h
  exact h
