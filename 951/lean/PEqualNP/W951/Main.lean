import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Hard

/-! Removable-NOT reduction: if the NOT gate can be replaced by a constant without changing any
output, the monotone charge applies (`bound_const`; used by `MinCE.essential`). -/

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

theorem constNot_mono (b : GateOp) (hb : b = GateOp.and ∨ b = GateOp.or) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ gates.map (constNot b), (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg'
  obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg'
  have hop := (hg g0 h0).1
  have hlen := (hg g0 h0).2
  cases g0 with
  | mk op ins =>
    simp only at hop hlen
    rcases hop with rfl | rfl | rfl
    · simp [constNot, hlen]
    · simp [constNot, hlen]
    · rcases hb with rfl | rfl <;> simp [constNot]

theorem good_of_mono {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Q : Finset (Fin n)) : Good Q gs := by
  intro pre g rest h
  exact Or.inl (hm g (by rw [h]; simp))

theorem bound_const {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate)
    (out : Fin m → ℕ) (b : GateOp) (hb : b = GateOp.and ∨ b = GateOp.or)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val (gates.map (constNot b)) x (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  have h := L951_core S (gates.map (constNot b)) out hev
    (charge_of_good S (gates.map (constNot b)) out hS hev
      (fun w => good_of_mono _ (constNot_mono b hb gates hg) (S w)))
  simpa using h

end PEqualNP.Outside.L_meta_951_aux
