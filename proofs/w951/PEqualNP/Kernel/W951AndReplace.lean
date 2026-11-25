import PEqualNP.Kernel.W951Privacy
import PEqualNP.Kernel.AndReplace

/-!
# Kernel/W951AndReplace: the exact Nechiporuk bound for W951's monotone list circuits

`Dag.sum_card_sub_one_le_andOr` (Wegener, Theorem 6.2, `h = k = 1`, at a base point) transported
through the total bridge `ofList`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside

/-- **Wegener's Theorem 6.2 (`(1,1)`-disjoint Boolean sums) for W951 list circuits, at base
`z`.** A monotone (AND/OR) list circuit of fan-in `≤ 2` whose wires `o w` (`w ∈ T`, in range)
compute `OR (S w)` on `{x ≥ z}` (each `S w` missing `z`), pairwise sharing at most one variable,
has `Σ_{w ∈ T} (|S w| − 1) ≤ gates.length`. -/
theorem sum_card_sub_one_le_length_andOr {n : ℕ} (gates : List LGate)
    (hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (z : Fin n → Bool) {ι : Type*} (T : Finset ι) (o : ι → ℕ) (S : ι → Finset (Fin n))
    (hrange : ∀ w ∈ T, o w < n + gates.length)
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → L_meta_951_aux.val gates x (o w) = Dag.orOf (S w) x)
    (hz : ∀ w ∈ T, Dag.orOf (S w) z = false) :
    ∑ w ∈ T, ((S w).card - 1) ≤ gates.length := by
  classical
  let D : Dag n gates.length := ofList gates gates.length
  rcases T.eq_empty_or_nonempty with hT | ⟨w0, hw0⟩
  · simp [hT]
  have hpos : 0 < n + gates.length := Nat.lt_of_le_of_lt (Nat.zero_le _) (hrange w0 hw0)
  let o' : ι → Fin (n + gates.length) := fun w =>
    if h : o w < n + gates.length then ⟨o w, h⟩ else ⟨0, hpos⟩
  have ho' : ∀ w ∈ T, ∀ x, z ≤ x → D.val x (o' w) = Dag.orOf (S w) x := by
    intro w hw x hx
    have hr := hrange w hw
    simp only [o', hr, dite_true]
    rw [ofList_val gates x]
    exact ho w hw x hx
  exact D.sum_card_sub_one_le_andOr
    (fun i => getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or) hop (Or.inr rfl) i)
    (ofList_fanin gates _ hfan) z T o' S hdisj ho' hz

end PEqualNP.Kernel
