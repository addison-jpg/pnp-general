import PEqualNP.Kernel.W951Minimal

/-!
# Kernel/W951Cube: restriction of a W951 list circuit to a subcube

`list_restrictVar` / `restrictVar_bound` (one variable) for a partial assignment: `Z` a set of
variables, `ρ` their values, `Cube Z ρ x ↔ ∀ t ∈ Z, x t = ρ t`, `proj Z ρ x` = `x` overwritten by
`ρ` on `Z`.

* `Dag.val_simplify_cube`: an output of `D.simplify (Cube Z ρ) O` carries, on EVERY input `x`, the
  value of the original output at `proj Z ρ x` (the simplified dag reads no variable of `Z`).
* `deadLC`, `list_restrictCube`: list form, exact size `|gates'| + #deadLC Z ρ O = |gates|`.
* `mem_deadLC_of_copy`, `mem_deadLC_of_const`: a gate equal on the cube to an earlier wire, or
  constant on the cube, is dead.
* `restrictCube_bound`: from a bound `B` for shorter circuits,
  `∑_{w ∈ I} (|S w \ Z| - 1) + #deadLC ≤ |gates|`, `I` = the sets with `|S w \ Z| ≥ 2` that are not
  set to `1` (no `t ∈ S w ∩ Z` with `ρ t = true`).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside
open PEqualNP.Outside.L_meta_951_aux (AtMostOneNot)

local notation "lval" => L_meta_951_aux.val

variable {n : ℕ}

/-- The subcube `{x | x = ρ on Z}`. -/
def Cube (Z : Finset (Fin n)) (ρ : Fin n → Bool) (x : Fin n → Bool) : Prop := ∀ t ∈ Z, x t = ρ t

open Classical in
/-- `x` overwritten by `ρ` on `Z`. -/
noncomputable def proj (Z : Finset (Fin n)) (ρ : Fin n → Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun t => if t ∈ Z then ρ t else x t

theorem cube_proj (Z : Finset (Fin n)) (ρ x : Fin n → Bool) : Cube Z ρ (proj Z ρ x) :=
  fun t ht => by simp [proj, ht]

theorem proj_notMem (Z : Finset (Fin n)) (ρ x : Fin n → Bool) {t : Fin n} (ht : t ∉ Z) :
    proj Z ρ x t = x t := by simp [proj, ht]

theorem proj_of_cube {Z : Finset (Fin n)} {ρ x : Fin n → Bool} (h : Cube Z ρ x) :
    proj Z ρ x = x := by
  funext t
  by_cases ht : t ∈ Z
  · simp [proj, ht, h t ht]
  · simp [proj, ht]

namespace Dag

variable {s : ℕ}

theorem isConst_cubeVar (D : Dag n s) (Z : Finset (Fin n)) (ρ : Fin n → Bool) (t : Fin n)
    (ht : t ∈ Z) : D.IsConst (Cube Z ρ) (Fin.castAdd s t) :=
  ⟨ρ t, fun x hx => by simp [hx t ht]⟩

/-- **Cube restriction, on all inputs.** Every output is constant on the cube, or is a wire of
`simplify (Cube Z ρ) O` which, on EVERY input `x`, carries the value of the original output at
`proj Z ρ x`. -/
theorem val_simplify_cube (D : Dag n s) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Fin (n + s) → Prop) (o : Fin (n + s)) (ho : O o) :
    D.IsConst (Cube Z ρ) o ∨
      ∃ o' : Fin (n + (D.liveGates (Cube Z ρ) O).card),
        ∀ x, (D.simplify (Cube Z ρ) O).val x o' = D.val (proj Z ρ x) o := by
  by_cases h : D.IsConst (Cube Z ρ) o
  · exact Or.inl h
  right
  rcases val_simplify (A := Cube Z ρ) O o ho with h' | ⟨o', ho', hv⟩
  · exact absurd h' h
  refine ⟨o', fun x => ?_⟩
  rw [← hv _ (cube_proj Z ρ x)]
  refine agree_off _ x _ (fun w => ∃ t ∈ Z, ew _ w = Fin.castAdd s t) (fun j hj => ?_)
    (fun t _ a ha hbad => ?_) o' ?_
  · rw [proj_notMem]
    intro hjZ
    exact hj ⟨j, hjZ, by rw [ew_castAdd]⟩
  · obtain ⟨t', ht', hbad⟩ := hbad
    obtain ⟨a', ha', he⟩ := mem_reads_keep ha
    have hb2 := he.symm.trans hbad
    exact (canon_of_mem_reads_prop ha').2 (by rw [hb2]; exact D.isConst_cubeVar Z ρ t' ht')
  · rintro ⟨t', ht', hbad⟩
    rw [ho'] at hbad
    exact (canon_rep h).2 (by rw [hbad]; exact D.isConst_cubeVar Z ρ t' ht')

end Dag

/-- The gates that die under the restriction to `Cube Z ρ` with outputs `O` (as indices). -/
noncomputable def deadLC (gates : List LGate) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Finset ℕ) : Finset ℕ :=
  ((ofList gates gates.length : Dag n _).deadGates (Cube Z ρ)
    fun w => w.1 ∈ O).map Fin.valEmbedding

/-- **Cube restriction, list form.** -/
theorem list_restrictCube (gates : List LGate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (Z : Finset (Fin n)) (ρ : Fin n → Bool) (O : Finset ℕ) :
    ∃ (gates' : List LGate) (e r : ℕ → ℕ),
      gates'.length + (deadLC gates Z ρ O).card = gates.length ∧ ShapeMap gates gates' e ∧
      ∀ o ∈ O, (∃ c, ∀ x : Fin n → Bool, Cube Z ρ x → lval gates x o = c) ∨
        ∀ x : Fin n → Bool, lval gates' x (r o) = lval gates (proj Z ρ x) o := by
  set G : Dag n gates.length := ofList gates gates.length
  set A : (Fin n → Bool) → Prop := Cube Z ρ
  set P : Fin (n + gates.length) → Prop := fun w => w.1 ∈ O
  have hNT : NoTrue (G.simplify A P) := by
    intro t
    refine Dag.keep_const_true _ _ _ (Dag.prop_const_true _ ?_)
    rw [ofList_gate, conv_op]
    exact getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
      hops (Or.inr (Or.inl rfl)) _
  have hex : ∀ o, ∃ o' : ℕ, o ∈ O → ((∃ c, ∀ x : Fin n → Bool, Cube Z ρ x → lval gates x o = c) ∨
      ∀ x : Fin n → Bool, lval (toList (G.simplify A P)) x o' =
        lval gates (proj Z ρ x) o) := by
    intro o
    by_cases hw : o < n + gates.length
    · by_cases ho : o ∈ O
      · rcases G.val_simplify_cube Z ρ P ⟨o, hw⟩ ho with ⟨c, hc⟩ | ⟨o', ho'⟩
        · exact ⟨0, fun _ => Or.inl ⟨c, fun x hx =>
            (ofList_val gates x ⟨o, hw⟩).symm.trans (hc x hx)⟩⟩
        · refine ⟨o'.1, fun _ => Or.inr fun x => ?_⟩
          rw [val_toList_wire _ hNT, ho', ofList_val]
      · exact ⟨0, fun h => absurd h ho⟩
    · exact ⟨0, fun _ => Or.inl ⟨false, fun x _ => val_ge_viaDag _ x _ (by omega)⟩⟩
  choose r hr using hex
  refine ⟨_, _, r, ?_, shapeMap_keep gates (G.prop A) ?_ _, fun o ho => hr o ho⟩
  · rw [toList_length, deadLC, Finset.card_map]
    exact G.card_simplify A P
  · intro j
    obtain ⟨h1, h2⟩ := Dag.prop_gate_shape (D := G) (A := A) j
    obtain ⟨-, g2⟩ := GS_ofList (n := n) gates j
    have g1 : (G.gate j).op = gates[j].op := by
      rw [ofList_gate, List.getD_eq_getElem _ _ j.2]; rfl
    refine ⟨?_, h2.trans g2⟩
    rcases h1 with h1 | h1
    · exact Or.inl (h1.trans g1)
    · exact Or.inr h1

theorem mem_deadLC_of_constOrCopy (gates : List LGate) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Finset ℕ) (k : ℕ) (hk : k < gates.length)
    (h : (ofList gates gates.length : Dag n _).ConstOrCopy (Cube Z ρ) ⟨k, hk⟩) :
    k ∈ deadLC gates Z ρ O :=
  Finset.mem_map.mpr ⟨⟨k, hk⟩, Dag.mem_deadGates_of_constOrCopy h, rfl⟩

/-- A gate equal, on the cube, to an earlier wire is dead. -/
theorem mem_deadLC_of_copy (gates : List LGate) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Finset ℕ) (k : ℕ) (hk : k < gates.length) (j : ℕ) (hj : j < n + k)
    (h : ∀ x : Fin n → Bool, Cube Z ρ x → lval gates x (n + k) = lval gates x j) :
    k ∈ deadLC gates Z ρ O := by
  refine mem_deadLC_of_constOrCopy gates Z ρ O k hk
    (Dag.constOrCopy_of_copy (u := ⟨j, by omega⟩) (by rw [Fin.lt_def]; simpa using hj)
      fun x hx => ?_)
  rw [ofList_val, ofList_val]
  exact (h x hx).symm

/-- A gate constant on the cube is dead. -/
theorem mem_deadLC_of_const (gates : List LGate) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Finset ℕ) (k : ℕ) (hk : k < gates.length) (c : Bool)
    (h : ∀ x : Fin n → Bool, Cube Z ρ x → lval gates x (n + k) = c) :
    k ∈ deadLC gates Z ρ O :=
  mem_deadLC_of_constOrCopy gates Z ρ O k hk
    (Dag.constOrCopy_of_const fun x hx => by rw [ofList_val]; exact h x hx)

theorem deadLC_lt (gates : List LGate) (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (O : Finset ℕ) (k : ℕ) (h : k ∈ deadLC gates Z ρ O) : k < gates.length := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp h
  exact i.2

/-- **Cube restriction bound.** Given a lower bound `B` for circuits shorter than `gates` (e.g.
`MinCE.bound_lt`), a correct circuit with at least one dead gate under the restriction to
`Cube Z ρ` satisfies `∑_{w ∈ I} (|S w \ Z| - 1) + #deadLC ≤ |gates|`, where `I` are the sets with
`|S w \ Z| ≥ 2` that are not set to `1`. -/
theorem restrictCube_bound {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List LGate)
    (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), lval gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List LGate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool), lval gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (Z : Finset (Fin n)) (ρ : Fin n → Bool)
    (hd : 1 ≤ (deadLC gates Z ρ (Finset.univ.image out)).card) :
    ∑ w ∈ Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card ∧ ∀ t ∈ S w, t ∈ Z → ρ t = false),
        ((S w \ Z).card - 1) + (deadLC gates Z ρ (Finset.univ.image out)).card ≤
      gates.length := by
  classical
  set I := Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card ∧ ∀ t ∈ S w, t ∈ Z → ρ t = false)
  obtain ⟨gates', e, r, hlen, hsh, hval⟩ := list_restrictCube gates (fun g hg' => (hg g hg').1)
    Z ρ (Finset.univ.image out)
  have hI : ∀ w ∈ I, ∀ x : Fin n → Bool,
      lval gates' x (r (out w)) = decide (∃ u ∈ S w \ Z, x u = true) := by
    intro w hw x
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hw2, hwb⟩ := hw
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (S w \ Z).card)
    have huZ : u ∉ Z := (Finset.mem_sdiff.mp hu).2
    have hev' : ∀ y : Fin n → Bool, Cube Z ρ y →
        lval gates y (out w) = decide (∃ u ∈ S w \ Z, y u = true) := by
      intro y hy
      rw [hev]
      congr 1
      apply propext
      constructor
      · rintro ⟨u', hu', hy'⟩
        refine ⟨u', Finset.mem_sdiff.mpr ⟨hu', fun hZ => ?_⟩, hy'⟩
        rw [hy u' hZ, hwb u' hu' hZ] at hy'; cases hy'
      · rintro ⟨u', hu', hy'⟩; exact ⟨u', (Finset.mem_sdiff.mp hu').1, hy'⟩
    rcases hval (out w) (Finset.mem_image_of_mem _ (Finset.mem_univ w)) with ⟨c, hc⟩ | hc
    · exfalso
      set x0 : Fin n → Bool := proj Z ρ (fun _ => false)
      set x1 : Fin n → Bool := proj Z ρ (Function.update (fun _ => false) u true)
      have e0 := (hev' x0 (cube_proj _ _ _)).symm.trans (hc x0 (cube_proj _ _ _))
      have e1 := (hev' x1 (cube_proj _ _ _)).symm.trans (hc x1 (cube_proj _ _ _))
      have h0 : decide (∃ u' ∈ S w \ Z, x0 u' = true) = false := by
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro u' hu'
        simp [x0, proj_notMem Z ρ _ (Finset.mem_sdiff.mp hu').2]
      have h1 : decide (∃ u' ∈ S w \ Z, x1 u' = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨u, hu, by simp [x1, proj_notMem Z ρ _ huZ]⟩
      rw [h0] at e0
      rw [h1, ← e0] at e1
      cases e1
    · rw [hc x, hev' _ (cube_proj _ _ _)]
      congr 1
      apply propext
      constructor
      · rintro ⟨u', hu', hy'⟩
        exact ⟨u', hu', by rwa [proj_notMem Z ρ _ (Finset.mem_sdiff.mp hu').2] at hy'⟩
      · rintro ⟨u', hu', hy'⟩
        exact ⟨u', hu', by rwa [proj_notMem Z ρ _ (Finset.mem_sdiff.mp hu').2]⟩
  let eI : Fin I.card ≃ I := I.equivFin.symm
  have hB := B I.card (fun i => S (eI i).1 \ Z) gates' (fun i => r (out (eI i).1))
    (by omega)
    (fun i => by
      have := (eI i).2
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.1)
    (fun i j hij => by
      have hne : (eI i).1 ≠ (eI j).1 := fun h => hij (eI.injective (Subtype.ext h))
      refine le_trans (Finset.card_le_card ?_) (hS _ _ hne)
      intro t ht
      simp only [Finset.mem_inter, Finset.mem_sdiff] at ht
      exact Finset.mem_inter.mpr ⟨ht.1.1, ht.2.1⟩)
    (hsh.hg hg) (hsh.hU hU) (fun i x => hI _ (eI i).2 x)
  have hsum : ∑ i : Fin I.card, ((S (eI i).1 \ Z).card - 1) =
      ∑ w ∈ I, ((S w \ Z).card - 1) := by
    exact PEqualNP.Base.Matching.sum_equivFin I (fun w => ((S w \ Z).card - 1))
  omega

/-! ## The zero-set case `ρ = 0` (moved from `W951/Peel2.lean`, statements unchanged)

The restriction `x_Z := 0` for a point set `Z` is the cube restriction with `ρ = 0`; the lemmas
below are its instances. -/

/-- `x` with the variables of `Z` set to `false`. -/
def zeroOn (Z : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun t => if t ∈ Z then false else x t

theorem zeroOn_mem (Z : Finset (Fin n)) (x : Fin n → Bool) : ∀ u ∈ Z, zeroOn Z x u = false :=
  fun u hu => by simp [zeroOn, hu]

theorem zeroOn_not_mem (Z : Finset (Fin n)) (x : Fin n → Bool) {u : Fin n} (hu : u ∉ Z) :
    zeroOn Z x u = x u := by simp [zeroOn, hu]

/-- `zeroOn` is `proj` with `ρ = 0`. -/
theorem zeroOn_eq_proj (Z : Finset (Fin n)) (x : Fin n → Bool) :
    zeroOn Z x = proj Z (fun _ => false) x := by
  funext t
  by_cases ht : t ∈ Z <;> simp [zeroOn, proj, ht]

namespace Dag

variable {s : ℕ}

theorem isConst_zeroSet (D : Dag n s) (Z : Finset (Fin n)) (v : Fin n) (hv : v ∈ Z) :
    D.IsConst (fun x => ∀ u ∈ Z, x u = false) (Fin.castAdd s v) :=
  D.isConst_cubeVar Z (fun _ => false) v hv

/-- **Set restriction, on all inputs** (the set version of `val_restrictVar`). Every output is
constant on `{x | x = 0 on Z}`, or is a wire of the simplified dag which, on EVERY input `x`,
carries the value of the original output at `x` with `x_Z := 0`. -/
theorem val_restrictZero (D : Dag n s) (Z : Finset (Fin n)) (O : Fin (n + s) → Prop)
    (o : Fin (n + s)) (ho : O o) :
    D.IsConst (fun x => ∀ u ∈ Z, x u = false) o ∨
      ∃ o' : Fin (n + (D.liveGates (fun x => ∀ u ∈ Z, x u = false) O).card),
        ∀ x, (D.simplify (fun x => ∀ u ∈ Z, x u = false) O).val x o' =
          D.val (zeroOn Z x) o := by
  rcases D.val_simplify_cube Z (fun _ => false) O o ho with h | ⟨o', h⟩
  · exact Or.inl h
  · exact Or.inr ⟨o', fun x => by rw [zeroOn_eq_proj]; exact h x⟩

end Dag

/-- The gates that die under `x_Z := 0` with outputs `O` (as indices). -/
noncomputable def deadZ (gates : List LGate) (Z : Finset (Fin n)) (O : Finset ℕ) : Finset ℕ :=
  ((ofList gates gates.length : Dag n _).deadGates (fun x => ∀ u ∈ Z, x u = false)
    fun w => w.1 ∈ O).map Fin.valEmbedding

theorem deadZ_eq_deadLC (gates : List LGate) (Z : Finset (Fin n)) (O : Finset ℕ) :
    deadZ gates Z O = deadLC gates Z (fun _ => false) O := rfl

/-- **Set restriction, list form** (the set version of `list_restrictVar`). -/
theorem list_restrictZero (gates : List LGate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (Z : Finset (Fin n)) (O : Finset ℕ) :
    ∃ (gates' : List LGate) (e r : ℕ → ℕ),
      gates'.length + (deadZ gates Z O).card = gates.length ∧ ShapeMap gates gates' e ∧
      ∀ o ∈ O, (∃ c, ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) → lval gates x o = c) ∨
        ∀ x : Fin n → Bool, lval gates' x (r o) = lval gates (zeroOn Z x) o := by
  obtain ⟨gates', e, r, hlen, hsh, hO⟩ := list_restrictCube gates hops Z (fun _ => false) O
  refine ⟨gates', e, r, hlen, hsh, fun o ho => ?_⟩
  rcases hO o ho with h | h
  · exact Or.inl h
  · exact Or.inr fun x => by rw [zeroOn_eq_proj]; exact h x

/-- A gate equal, on `{x | x = 0 on Z}`, to an earlier wire is dead. -/
theorem mem_deadZ_of_copy (gates : List LGate) (Z : Finset (Fin n)) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length) (j : ℕ) (hj : j < n + k)
    (h : ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) → lval gates x (n + k) = lval gates x j) :
    k ∈ deadZ gates Z O :=
  mem_deadLC_of_copy gates Z (fun _ => false) O k hk j hj h

/-- A gate constant on `{x | x = 0 on Z}` is dead. -/
theorem mem_deadZ_of_const (gates : List LGate) (Z : Finset (Fin n)) (O : Finset ℕ)
    (k : ℕ) (hk : k < gates.length) (c : Bool)
    (h : ∀ x : Fin n → Bool, (∀ u ∈ Z, x u = false) → lval gates x (n + k) = c) :
    k ∈ deadZ gates Z O :=
  mem_deadLC_of_const gates Z (fun _ => false) O k hk c h

/-- **Set restriction bound** (the set version of `restrictVar_bound`, `b = false`). Given a lower
bound `B` for circuits shorter than `gates`, a correct circuit with at least one dead gate under
`x_Z := 0` satisfies `∑_{w ∈ I} (|S w \ Z| - 1) + #deadZ Z ≤ |gates|`, `I` = the sets with
`|S w \ Z| ≥ 2`. -/
theorem restrictZero_bound {m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List LGate)
    (out : Fin m → ℕ)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool), lval gates x (out w) = decide (∃ u ∈ S w, x u = true))
    (B : ∀ (m' : ℕ) (S' : Fin m' → Finset (Fin n)) (gates' : List LGate) (out' : Fin m' → ℕ),
      gates'.length < gates.length →
      (∀ i : Fin m', 2 ≤ (S' i).card) → (∀ i j : Fin m', i ≠ j → (S' i ∩ S' j).card ≤ 1) →
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates' →
      (∀ (w : Fin m') (x : Fin n → Bool), lval gates' x (out' w) = decide (∃ u ∈ S' w, x u = true)) →
      ∑ i : Fin m', ((S' i).card - 1) ≤ gates'.length)
    (Z : Finset (Fin n)) (hd : 1 ≤ (deadZ gates Z (Finset.univ.image out)).card) :
    ∑ w ∈ Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card), ((S w \ Z).card - 1) +
        (deadZ gates Z (Finset.univ.image out)).card ≤ gates.length := by
  have h := restrictCube_bound S gates out hS hg hU hev B Z (fun _ => false) hd
  have hf : Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card ∧
      ∀ t ∈ S w, t ∈ Z → (fun _ : Fin n => false) t = false) =
      Finset.univ.filter (fun w => 2 ≤ (S w \ Z).card) :=
    Finset.filter_congr fun w _ => by simp
  rw [hf] at h
  exact h

end PEqualNP.Kernel
