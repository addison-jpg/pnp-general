import PEqualNP.Kernel.W951Cube

/-!
# Kernel/W951CubeKeep: the gate-level form of the cube restriction

`list_restrictCube` (W951Cube) states the restriction of a list circuit to a subcube `Cube Z ρ`
output by output. With EVERY wire an output, the restricted list keeps exactly the gates that are
neither constant nor a copy of an earlier wire on the cube, in order, with their values:

* `list_restrictCube_keep`: a restricted list `gates'` and a kept-gate map `e` (`ShapeMap`, so
  strictly increasing, with the 951 gate shapes) such that kept gate `t` has, on the cube, the value
  of gate `e t`, and every gate of `gates` that is not kept is constant on the cube or equal there to
  an earlier wire.

These are the hypotheses of `W951/RunTransfer.run_transfer` (union-find runs at points of the cube).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside

local notation "lval" => L_meta_951_aux.val

variable {n : ℕ}

/-- **Cube restriction, gate by gate.** -/
theorem list_restrictCube_keep (gates : List LGate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (Z : Finset (Fin n)) (ρ : Fin n → Bool) :
    ∃ (gates' : List LGate) (e : ℕ → ℕ), ShapeMap gates gates' e ∧
      (∀ t < gates'.length, ∀ x : Fin n → Bool, Cube Z ρ x →
        lval gates' x (n + t) = lval gates x (n + e t)) ∧
      (∀ k < gates.length, (∀ t < gates'.length, e t ≠ k) →
        (∃ c, ∀ x : Fin n → Bool, Cube Z ρ x → lval gates x (n + k) = c) ∨
        (∃ j < n + k, ∀ x : Fin n → Bool, Cube Z ρ x →
          lval gates x (n + k) = lval gates x j)) := by
  set G : Dag n gates.length := ofList gates gates.length
  set A : (Fin n → Bool) → Prop := Cube Z ρ
  set P : Fin (n + gates.length) → Prop := fun _ => True
  set K := G.liveGates A P with hK
  have hNT : NoTrue (G.simplify A P) := by
    intro t
    refine Dag.keep_const_true _ _ _ (Dag.prop_const_true _ ?_)
    rw [ofList_gate, conv_op]
    exact getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
      hops (Or.inr (Or.inl rfl)) _
  have hshape : ∀ j : Fin gates.length, GS ((G.prop A).gate j) gates[j] := by
    intro j
    obtain ⟨h1, h2⟩ := Dag.prop_gate_shape (D := G) (A := A) j
    obtain ⟨-, g2⟩ := GS_ofList (n := n) gates j
    have g1 : (G.gate j).op = gates[j].op := by
      rw [ofList_gate, List.getD_eq_getElem _ _ j.2]; rfl
    refine ⟨?_, h2.trans g2⟩
    rcases h1 with h1 | h1
    · exact Or.inl (h1.trans g1)
    · exact Or.inr h1
  have hlen : (toList (G.simplify A P)).length = K.card := toList_length _
  refine ⟨toList (G.simplify A P), fun t => if h : t < K.card then (Dag.kemb K ⟨t, h⟩).1 else 0,
    shapeMap_keep gates (G.prop A) hshape K, ?_, ?_⟩
  · intro t ht x hx
    have ht' : t < K.card := by rw [← hlen]; exact ht
    simp only [dite_eq_left ht']
    have h1 := val_toList_wire (G.simplify A P) hNT x (Fin.natAdd n ⟨t, ht'⟩)
    have h2 : (G.simplify A P).val x (Fin.natAdd n ⟨t, ht'⟩) =
        (G.prop A).val x (Dag.ew K (Fin.natAdd n ⟨t, ht'⟩)) :=
      Dag.val_keep (G.prop A) K ((G.prop A).coneGates_closed (G.outReps A P)) x _
    rw [Dag.ew_natAdd] at h2
    have h3 := Dag.val_prop (D := G) (A := A) hx (Fin.natAdd n (Dag.kemb K ⟨t, ht'⟩))
    have h4 := ofList_val gates x (Fin.natAdd n (Dag.kemb K ⟨t, ht'⟩))
    simp only [Fin.val_natAdd] at h1 h4
    rw [h1, h2, h3, h4]
  · intro k hk hne
    have hlive : (⟨k, hk⟩ : Fin gates.length) ∉ K := by
      intro hmem
      have hr := (Dag.krank K _ hmem).2
      apply hne (Dag.krank K _ hmem).1 (by rw [hlen]; exact hr)
      simp only [dite_eq_left hr, Fin.eta, Dag.kemb_krank]
    by_cases hc : G.IsConst A (Fin.natAdd n ⟨k, hk⟩)
    · obtain ⟨c, hc⟩ := hc
      refine Or.inl ⟨c, fun x hx => ?_⟩
      have h4 := ofList_val gates x (Fin.natAdd n ⟨k, hk⟩)
      simp only [Fin.val_natAdd] at h4
      rw [← h4]
      exact hc x hx
    · right
      have hrep : G.rep A (Fin.natAdd n ⟨k, hk⟩) ≠ Fin.natAdd n ⟨k, hk⟩ := by
        intro hr
        apply hlive
        rw [hK, Dag.liveGates, Dag.mem_coneGates]
        exact (G.prop A).subset_cone (G.outReps A P) ⟨_, trivial, hc, hr⟩
      have hjle := Dag.rep_le (D := G) (A := A) (Fin.natAdd n ⟨k, hk⟩)
      have hjlt : (G.rep A (Fin.natAdd n ⟨k, hk⟩)).1 < n + k := by
        have := lt_of_le_of_ne hjle hrep
        rw [Fin.lt_def] at this
        simpa using this
      refine ⟨_, hjlt, fun x hx => ?_⟩
      have hs := Dag.rep_same (D := G) (A := A) (Fin.natAdd n ⟨k, hk⟩) x hx
      have h4 := ofList_val gates x (Fin.natAdd n ⟨k, hk⟩)
      have h5 := ofList_val gates x (G.rep A (Fin.natAdd n ⟨k, hk⟩))
      simp only [Fin.val_natAdd] at h4
      rw [← h4, ← h5]
      exact hs.symm

end PEqualNP.Kernel
