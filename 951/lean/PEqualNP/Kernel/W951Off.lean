import PEqualNP.Kernel.W951Core

/-!
# Kernel/W951Off: list-model transfer off one wire

`listVal_rel_off`: two inputs related (by a reflexive `R`) off wire `p` stay related at every wire
but `p` of a list circuit, if each gate either relates its two values outright or maps reads
related off `p` to related values. Proved on the dag by `Dag.wire_induction` and moved to W951's
list fold by `ofList_valN`. Its `R = Eq` instance is W951's "no live gate reads wire `p`, so the
values agree" (`Restrict.val_congr_of_insens`).
-/

namespace PEqualNP.Kernel

open PEqualNP.Outside.L_meta_951_aux (val)

theorem listVal_rel_off {n : ℕ} (R : Bool → Bool → Prop) (hR : ∀ b, R b b) (p : ℕ)
    (gs : List LGate) (x y : Fin n → Bool) (hxy : ∀ j : Fin n, (j : ℕ) ≠ p → R (x j) (y j))
    (h : ∀ (k : ℕ) (hk : k < gs.length), R (val gs x (n + k)) (val gs y (n + k)) ∨
      ∀ f f' : ℕ → Bool, (∀ i, i ≠ p → R (f i) (f' i)) →
        R ((gs[k]'hk).op.eval ((gs[k]'hk).inputs.map f))
          ((gs[k]'hk).op.eval ((gs[k]'hk).inputs.map f'))) :
    ∀ i, i ≠ p → R (val gs x i) (val gs y i) := by
  intro i hi
  rw [← ofList_valN gs x i, ← ofList_valN gs y i]
  by_cases hlt : i < n + gs.length
  swap
  · rw [Dag.valN_of_ge _ _ (not_lt.mp hlt), Dag.valN_of_ge _ _ (not_lt.mp hlt)]; exact hR false
  rw [Dag.valN_of_lt _ _ hlt, Dag.valN_of_lt _ _ hlt]
  revert hi
  refine Dag.wire_induction (P := fun w => w.1 ≠ p → R ((ofList gs gs.length : Dag n _).val x w)
    ((ofList gs gs.length : Dag n _).val y w)) (fun j hj => by simpa using hxy j hj)
    (fun k ih hk => ?_) ⟨i, hlt⟩
  rcases h k k.2 with hd | hd
  · rw [ofList_val, ofList_val]; exact hd
  rw [Dag.val_natAdd, Dag.val_natAdd, ofList_gate, List.getD_eq_getElem _ _ k.2, conv_eval,
    conv_eval]
  refine hd _ _ fun j hj => ?_
  unfold rd
  split
  · exact ih _ hj
  · exact hR false

end PEqualNP.Kernel
