import Mathlib
import PEqualNP.Defs

/-!
# Shape of low fan-in gates

An AND/OR gate with at most two inputs is a constant, a copy of one wire, or a binary AND/OR of two
wires; a NOT gate is constant `true` (no input) or the negation of its first input.
-/

namespace PEqualNP.Kernel.GateShape

open PEqualNP.CircuitLowerBounds

/-- Arity split of a gate with at most two inputs. -/
theorem inputs_cases (g : Gate) (hlen : g.inputs.length ≤ 2) :
    g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ ∃ a b, g.inputs = [a, b] := by
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  · rw [h] at hlen; simp at hlen

/-- AND/OR gate shape, with the inputs matched explicitly. -/
theorem and_or_shape (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : ℕ → Bool) :
    (g.op = GateOp.and ∧ g.inputs = [] ∧ g.op.eval (g.inputs.map f) = true) ∨
    (g.op = GateOp.or ∧ g.inputs = [] ∧ g.op.eval (g.inputs.map f) = false) ∨
    (∃ a, g.inputs = [a] ∧ g.op.eval (g.inputs.map f) = f a) ∨
    (g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧ g.op.eval (g.inputs.map f) = (f a && f b)) ∨
    (g.op = GateOp.or ∧ ∃ a b, g.inputs = [a, b] ∧ g.op.eval (g.inputs.map f) = (f a || f b)) := by
  rcases inputs_cases g hlen with h | ⟨a, h⟩ | ⟨a, b, h⟩ <;> rcases hop with ho | ho
  · exact Or.inl ⟨ho, h, by simp [h, ho, GateOp.eval]⟩
  · exact Or.inr (Or.inl ⟨ho, h, by simp [h, ho, GateOp.eval]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h, by simp [h, ho, GateOp.eval]⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a, h, by simp [h, ho, GateOp.eval]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ho, a, b, h, by simp [h, ho, GateOp.eval]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ho, a, b, h, by simp [h, ho, GateOp.eval]⟩)))

/-- NOT gate shape (`length ≤ 2` is not needed: further inputs are ignored). -/
theorem not_shape (g : Gate) (hop : g.op = GateOp.not) (_hlen : g.inputs.length ≤ 2)
    (f : ℕ → Bool) :
    (g.inputs = [] ∧ g.op.eval (g.inputs.map f) = true) ∨
    ∃ a r, g.inputs = a :: r ∧ g.op.eval (g.inputs.map f) = !(f a) := by
  rcases h : g.inputs with _ | ⟨a, r⟩
  · exact Or.inl ⟨rfl, by simp [hop, GateOp.eval]⟩
  · exact Or.inr ⟨a, r, rfl, by simp [hop, GateOp.eval]⟩

end PEqualNP.Kernel.GateShape
