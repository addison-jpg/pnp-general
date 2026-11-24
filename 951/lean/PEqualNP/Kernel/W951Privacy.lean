import PEqualNP.Kernel.W951Core
import PEqualNP.Kernel.Privacy

/-!
# Kernel/W951Privacy: Lemma 6.1 for W951's list circuits

The privacy / merge-count statements of `Kernel/Privacy.lean` transported through the total
bridge `ofList`: an OR-only list circuit of fan-in `≤ 2` whose output wires compute a
`(1,1)`-disjoint Boolean sum on the cube `{x ≥ z}` (in W951's `L_meta_951_aux.val`) has at least
`Σ_w (|S w| − 1)` gates.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside

/-- OR-only list circuits translate to OR-only dags. -/
theorem ofList_orOnly {n : ℕ} (gates : List LGate) (s : ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.or) : (ofList gates s : Dag n s).OrOnly :=
  fun i => getD_ind (P := fun g => g.op = GateOp.or) hg rfl i

/-- The fan-in bound transfers through the bridge. -/
theorem ofList_fanin {n : ℕ} (gates : List LGate) (s : ℕ) {r : ℕ}
    (hg : ∀ g ∈ gates, g.inputs.length ≤ r) (i : Fin s) :
    ((ofList gates s : Dag n s).gate i).inputs.length ≤ r := by
  rw [ofList_gate, conv_inputs_length]
  exact getD_ind (P := fun g => g.inputs.length ≤ r) hg (by simp [dflt]) i

/-- **Lemma 6.1 (`(1,1)`-disjoint Boolean sums) for W951 list circuits, at base `z`.** An
OR-only list circuit of fan-in `≤ 2` whose wires `o w` (`w ∈ T`, in range) compute `OR (S w)` on
`{x ≥ z}` (each `S w` missing `z`), pairwise sharing at most one variable, has
`Σ_{w ∈ T} (|S w| − 1) ≤ gates.length`. -/
theorem sum_card_sub_one_le_length {n : ℕ} (gates : List LGate)
    (hor : ∀ g ∈ gates, g.op = GateOp.or) (hfan : ∀ g ∈ gates, g.inputs.length ≤ 2)
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
  exact ((ofList gates gates.length : Dag n _).sum_card_sub_one_le_gates
    (ofList_orOnly gates _ hor) (ofList_fanin gates _ hfan) z T o' S hdisj ho' hz).1.trans
    ((ofList gates gates.length : Dag n _).sum_card_sub_one_le_gates
    (ofList_orOnly gates _ hor) (ofList_fanin gates _ hfan) z T o' S hdisj ho' hz).2

end PEqualNP.Kernel
