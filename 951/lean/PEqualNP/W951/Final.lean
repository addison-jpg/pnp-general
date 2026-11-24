import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.MinCE

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

/-- The DD4 hard case in which every point lying in some set lies in at least two sets of size at
least 3 (after Two-World, T1 and R0'). Derived from the only open statement `no_minCE` (MinCE.lean);
conversely `MinCE.false_of_hardCaseCore` shows it implies `no_minCE`. -/
theorem hard_case_core : HardCaseCore := hardCaseCore_of_minCE

/-- The hard branch (the earlier open statement), derived from `no_minCE` like `hard_case_core`;
conversely `no_minCE_of_hardCase` (MinCE.lean) shows it implies `no_minCE`. -/
theorem hard_case : HardCase := by
  intro n m S h2 hS gates out hg hU hev _ _ _ _ _ _ _ _ _ hlt
  have := bound_of_noMinCE S h2 hS gates out hg hU hev
  omega

/-- The 951 bound from the hard case, without `no_minCE`: `HardCase → no_minCE`
(`no_minCE_of_hardCase`). The bridges `hardCase_of_gapG`, `hardCase_of_fracMatch` and
`hardCase_of_priceIneq` reach L-meta-951 through it. -/
theorem L_meta_951_of_hardCase (H : HardCase) : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact bound_of_forall_not_minCE (no_minCE_of_hardCase H) S h2 hS gates out hg (hU_of_ι hι) hev

/-- L-meta-951 from the core case alone, without `no_minCE` (`no_minCE_of_hardCaseCore`). -/
theorem L_meta_951_of_core (H : HardCaseCore) : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  intro n m S h2 hS gates out hg hι hev
  exact bound_of_forall_not_minCE (no_minCE_of_hardCaseCore H) S h2 hS gates out hg (hU_of_ι hι)
    hev

end PEqualNP.Outside.L_meta_951_aux

open PEqualNP.Outside.L_meta_951_aux in
theorem PEqualNP.Outside.L_meta_951 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length :=
  L_meta_951_of_minCE
