import Mathlib
import PEqualNP.Defs
import PEqualNP.W951.Eval

/-!
# Kernel/W951Extra: the list-model form of `Dag.val_le_val`

`Kernel/W951Bridge.lean` imports `W951/TwoWorld.lean` (it needs `constNot`, `C0`, `C1`), so
`W951/Cases.lean` and `W951/TwoWorld.lean` cannot import the bridge. Moreover `Cases.mono_val`
and `TwoWorld.sandwich` carry no arity hypothesis, while the bridge (`conv`) needs `≤ 2` inputs.
This file states the one kernel fact both need (`Dag.val_le_val`: gatewise-monotone related
circuits are wirewise related) directly on W951's `List Gate` fold, for any arity. It imports
only `W951/Eval.lean`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside.L_meta_951_aux (val val_nil val_snoc)

/-- An AND/OR list gate is monotone in the values it reads (any arity). -/
theorem listOp_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    {v v' : ℕ → Bool} (h : ∀ j, v j = true → v' j = true) :
    op.eval (ins.map v) = true → op.eval (ins.map v') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hh j hj => h j (hh j hj)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨j, hj, hv⟩ => ⟨j, hj, h j hv⟩

/-- List-model `Dag.val_le_val`: if gate by gate `f a` on smaller reads is below `g a` on larger
reads, then every wire of `gs.map f` at `x` is below the same wire of `gs.map g` at `y ≥ x`. -/
theorem listVal_le {n : ℕ} (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (f g : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate)
    (x y : Fin n → Bool)
    (hxy : ∀ c, x c = true → y c = true)
    (h : ∀ a ∈ gs, ∀ v v' : ℕ → Bool, (∀ j, v j = true → v' j = true) →
      (f a).op.eval ((f a).inputs.map v) = true → (g a).op.eval ((g a).inputs.map v') = true) :
    ∀ i, val (gs.map f) x i = true → val (gs.map g) y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [List.map_nil, val_nil] at hi ⊢
    split_ifs at hi ⊢ with hn
    exact hxy _ hi
  | append_singleton gs a ih =>
    have ih' := ih fun b hb => h b (List.mem_append_left _ hb)
    intro i
    simp only [List.map_append, List.map_cons, List.map_nil, val_snoc, List.length_map]
    split_ifs
    · exact h a (by simp) _ _ ih'
    · exact ih' i

end PEqualNP.Kernel
