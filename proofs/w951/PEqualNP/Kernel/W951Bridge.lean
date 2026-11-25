import PEqualNP.Kernel.W951Core
import PEqualNP.W951.TwoWorld

/-!
# Kernel/W951Bridge: W951 statements that need `Cases` / `Cone` / `TwoWorld` definitions

`Kernel/W951Core.lean` holds the bridge itself (`conv`, `ofList`, `ofList_valN`), which is total
and imports only `W951/Eval.lean`. This file imports `W951/TwoWorld.lean` (hence `Cases`,
`Cone`) for the definitions `constNot`, `C0`, `C1`, `mask`, `ReadClosed`, and re-proves the W951
statements about them from the kernel lemmas. No statement here has a fan-in hypothesis, and
the only hypotheses on operations are the ones the W951 statements themselves carry.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside

/-! ## `val_ge`, `val_gate` -/

/-- W951 `Charge.val_ge` / `MergeRun.mr_val_ge`: one line. -/
theorem val_ge_bridge {n : ℕ} (gs : List LGate) (x : Fin n → Bool)
    (j : ℕ) (hj : n + gs.length ≤ j) : L_meta_951_aux.val gs x j = false :=
  val_ge_viaDag gs x j hj

/-- W951 `Cone.val_gate` / `MergeRun.mr_val_gate`, in kernel form: a gate wire is the gate
applied to the earlier wires. -/
theorem val_gate_bridge {n : ℕ} (gs : List LGate) (x : Fin n → Bool)
    (j : ℕ) (hj : j < gs.length) :
    L_meta_951_aux.val gs x (n + j) =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun t =>
        if t < n + j then L_meta_951_aux.val gs x t else false) := by
  rw [← ofList_valN gs, Dag.valN_of_lt _ _ (by omega)]
  have e : (⟨n + j, by omega⟩ : Fin (n + gs.length)) = Fin.natAdd n ⟨j, hj⟩ := rfl
  rw [e, Dag.val_natAdd, ofList_gate, conv_eval, List.getD_eq_getElem _ _ hj]
  congr 1
  apply List.map_congr_left
  intro t _
  unfold rd
  split
  · next ht =>
    rw [← ofList_valN gs, Dag.valN_of_lt _ _ (by simp at ht; omega)]
    rfl
  · rfl

/-! ## `constNot`, the two worlds, the sandwich -/

/-- W951's `constNot` IS the kernel's `constNot` (`OR []` is `false`, `AND []` is `true`). -/
theorem conv_constNot_or (k : ℕ) (g : LGate) :
    conv k (L_meta_951_aux.constNot GateOp.or g) = (conv k g).constNot false := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

theorem conv_constNot_and (k : ℕ) (g : LGate) :
    conv k (L_meta_951_aux.constNot GateOp.and g) = (conv k g).constNot true := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

/-- W951's lower world `C0` is the kernel's `constNot false`: a syntactic equality of dags. -/
theorem ofList_C0 {n : ℕ} (gates : List LGate) (s : ℕ) :
    (ofList (L_meta_951_aux.C0 gates) s : Dag n s) = (ofList gates s).constNot false := by
  ext1
  funext i
  rw [ofList_gate, Dag.constNot_gate, ofList_gate, L_meta_951_aux.C0, getD_map_dflt _ rfl,
    conv_constNot_or]

/-- W951's upper world `C1` is the kernel's `constNot true`. -/
theorem ofList_C1 {n : ℕ} (gates : List LGate) (s : ℕ) :
    (ofList (L_meta_951_aux.C1 gates) s : Dag n s) = (ofList gates s).constNot true := by
  ext1
  funext i
  rw [ofList_gate, Dag.constNot_gate, ofList_gate, L_meta_951_aux.C1, getD_map_dflt _ rfl,
    conv_constNot_and]

/-- W951 `TwoWorld.sandwich`, exact statement (`C0 ≤ C ≤ C1` on every wire, any number of NOT
gates, any fan-in), from `Dag.sandwich`. -/
theorem sandwich_bridge {n : ℕ} (gates : List LGate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x : Fin n → Bool) :
    ∀ i, (L_meta_951_aux.val (L_meta_951_aux.C0 gates) x i = true →
        L_meta_951_aux.val gates x i = true) ∧
      (L_meta_951_aux.val gates x i = true →
        L_meta_951_aux.val (L_meta_951_aux.C1 gates) x i = true) := by
  have hD : ∀ s, (ofList gates s : Dag n s).MonoOffNot := fun s => ofList_monoOffNot gates s hg
  have h0 := listVal_rel_of_dag (L_meta_951_aux.C0 gates) gates (by simp [L_meta_951_aux.C0])
    x x (fun a b => a = true → b = true) id fun w => by
      rw [ofList_C0]
      exact Bool.le_iff_imp.mp ((Dag.sandwich _ (hD _) x w).1)
  have h1 := listVal_rel_of_dag gates (L_meta_951_aux.C1 gates) (by simp [L_meta_951_aux.C1])
    x x (fun a b => a = true → b = true) id fun w => by
      rw [ofList_C1]
      exact Bool.le_iff_imp.mp ((Dag.sandwich _ (hD _) x w).2)
  exact fun i => ⟨h0 i, h1 i⟩

/-! ## Monotonicity -/

/-- W951 `Cases.mono_val`, exact statement (AND/OR circuits of any fan-in are monotone), from
`Dag.val_mono`. -/
theorem mono_val_bridge {n : ℕ} (gs : List LGate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ c, x c = true → y c = true) :
    ∀ i, L_meta_951_aux.val gs x i = true → L_meta_951_aux.val gs y i = true :=
  mono_val_viaDag gs hg x y hxy

/-! ## Masks -/

theorem lmask_eq (K : Finset ℕ) (gs : List LGate) : lmask K gs = L_meta_951_aux.mask K gs := rfl

/-- W951's `mask` IS the kernel's `mask`: a syntactic equality of dags. -/
theorem ofList_mask {n : ℕ} (K : Finset ℕ) (gs : List LGate) (s : ℕ) :
    (ofList (L_meta_951_aux.mask K gs) s : Dag n s) = (ofList gs s).mask (wiresOf n s K) :=
  ofList_lmask K gs s

/-- W951 `Cone.val_mask`, exact statement (masking with a read-closed set keeps the wires of
the set), from `Dag.val_mask`. -/
theorem val_mask_bridge {n : ℕ} (K : Finset ℕ) (L : ℕ) (x : Fin n → Bool) :
    ∀ gs : List LGate, gs.length ≤ L → L_meta_951_aux.ReadClosed n L K gs →
      ∀ i, (i < n ∨ i - n ∈ K ∨ n + gs.length ≤ i) →
        L_meta_951_aux.val (L_meta_951_aux.mask K gs) x i = L_meta_951_aux.val gs x i :=
  val_mask_viaDag K L x

/-- W951 `Cone.val_mask_out`, exact statement (a masked-away gate is `false`), from
`Dag.val_mask_out`. -/
theorem val_mask_out_bridge {n : ℕ} (K : Finset ℕ) (gs : List LGate)
    (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (hjK : j ∉ K) :
    L_meta_951_aux.val (L_meta_951_aux.mask K gs) x (n + j) = false :=
  val_mask_out_viaDag K gs x j hj hjK

end PEqualNP.Kernel
