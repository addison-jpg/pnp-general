import PEqualNP.Kernel.W951Bridge
import PEqualNP.Kernel.W951AndReplace

/-!
# Kernel/W951TwoWorld: the exact Nechiporuk bound in each world of a one-NOT circuit

W951's setting: `gates : List Gate` with AND/OR/NOT gates of fan-in `≤ 2`, output wires `out w`
computing `OR (S w)` everywhere (`hev`), the sets pairwise sharing at most one variable. The
lower world `C0 gates` (every NOT := `false`, i.e. `OR []`) and the upper world `C1 gates`
(every NOT := `true`, i.e. `AND []`) are AND/OR circuits of fan-in `≤ 2` with the same number of
gates, so Wegener's Theorem 6.2 (`sum_card_sub_one_le_length_andOr`, via
`Dag.sum_card_sub_one_le_andOr`) applies to them wherever they agree with the circuit.

* `nech_interval_mono`: a monotone list circuit computing `OR (S w)` on an interval `[z, y]`
  (each `S w` missing `z`) has `Σ_w (|S w ∩ y| − 1)` gates. Proof: restrict the inputs outside
  `y` to `false` (`Dag.restrict`, same size, same operations and fan-ins); the restricted dag
  computes `OR (S w ∩ y)` on `{x ≥ z}`.
* `nech_interval`: the same for either world of a W951 circuit, where it agrees with the circuit.
* `nech_one_point` (`C0 = C` on `{x ≥ z}`): `Σ_{S w ∩ z = ∅} (|S w| − 1) ≤ gates.length`.
* `nech_zero_point` (`C1 = C` on `{x ≤ y}`): `Σ_w (|S w ∩ y| − 1) ≤ gates.length`.
* With at most one NOT (`AtMostOneNot`): the NOT output is antitone (its input is computed by
  the AND/OR prefix), so NOT `= 0` at `z` gives `C0 = C` on `{x ≥ z}` (`C0_agree_of_not_false`)
  and NOT `= 1` at `y` gives `C1 = C` on `{x ≤ y}` (`C1_agree_of_not_true`). Hence
  `nech_one_point_of_not`, `nech_zero_point_of_not`, the dichotomy `nech_two_world` (at every
  point one of the two bounds holds), the PartialBound-style forms with the NOT reading wire
  `hw` (`nech_one_point_of_input`: `hw(z) = 1`; `nech_zero_point_of_input`: `hw(y) = 0`) and
  the single-variable cases `z = eof k`, `y = Zof {k}`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside
open PEqualNP.Outside.L_meta_951_aux (val C0 C1 AtMostOneNot eof Zof)

/-! ## Helpers on the list model -/

/-- An input wire of the list fold is the input bit. -/
theorem listVal_input {n : ℕ} (gs : List LGate) (x : Fin n → Bool) (j : ℕ) (hj : j < n) :
    val gs x j = x ⟨j, hj⟩ := by
  have h := L_meta_951_aux.val_append [] gs x j (by simpa using hj)
  rw [List.nil_append] at h
  rw [h, L_meta_951_aux.val_nil]
  simp [hj]

/-- The restriction fixing the inputs outside `y` to `false`. -/
def downρ {n : ℕ} (y : Fin n → Bool) (j : Fin n) : Option Bool :=
  if y j = true then none else some false

theorem override_downρ {n : ℕ} (y x : Fin n → Bool) : Dag.override (downρ y) x = x ⊓ y := by
  funext j
  cases hy : y j <;> cases hx : x j <;> simp [Dag.override, downρ, hy, hx]

theorem orOf_inf {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) :
    Dag.orOf S (x ⊓ y) = Dag.orOf (S.filter fun i => y i = true) x := by
  simp only [Dag.orOf, Finset.mem_filter, Pi.inf_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨v, hv, h⟩
    have h' : x v = true ∧ y v = true := by simpa using h
    exact ⟨v, ⟨hv, h'.2⟩, h'.1⟩
  · rintro ⟨v, ⟨hv, hy⟩, hx⟩
    exact ⟨v, hv, by simp [hx, hy]⟩

/-- An output computing `OR S` on `[z, y]`, with `S` missing `z` and two points of `S` in `y`,
is a gate wire (not an input, not past the end). -/
theorem gate_wire_of_two {n : ℕ} (G : List LGate) (z y : Fin n → Bool) (hzy : z ≤ y) (o : ℕ)
    (S : Finset (Fin n)) (ho : ∀ x, z ≤ x → x ≤ y → val G x o = Dag.orOf S x)
    (hz : Dag.orOf S z = false) (h2 : 2 ≤ (S.filter fun i => y i = true).card) :
    n ≤ o ∧ o < n + G.length := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_filter] at hu hv
  have hup : ∀ u, u ∈ S → y u = true → val G (Function.update z u true) o = true := by
    intro u hu hyu
    rw [ho _ (Dag.le_update z u) ?_]
    · simp only [Dag.orOf, decide_eq_true_eq]
      exact ⟨u, hu, by simp⟩
    · intro j
      by_cases hj : j = u
      · subst hj; simp [hyu]
      · rw [Function.update_of_ne hj]; exact hzy j
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hz' := ho z le_rfl hzy
    rw [hz, listVal_input G z o hlt] at hz'
    have key : ∀ u, u ∈ S → y u = true → (⟨o, hlt⟩ : Fin n) = u := by
      intro u hu hyu
      have h := hup u hu hyu
      rw [listVal_input G _ o hlt] at h
      by_contra hne
      rw [Function.update_of_ne hne, hz'] at h
      exact absurd h (by simp)
    exact huv ((key u hu.1 hu.2).symm.trans (key v hv.1 hv.2))
  · by_contra hge
    push Not at hge
    have h := hup u hu.1 hu.2
    rw [val_ge_bridge G _ o hge] at h
    exact absurd h (by simp)

/-! ## The monotone bound on an interval -/

/-- **Wegener's Theorem 6.2 on an interval `[z, y]`.** A monotone (AND/OR) list circuit of
fan-in `≤ 2` whose wires `o w` (`w ∈ T`) compute `OR (S w)` on `{z ≤ x ≤ y}` (each `S w` missing
`z`), the sets pairwise sharing at most one variable, has
`Σ_{w ∈ T} (|S w ∩ y| − 1) ≤ G.length`. No range hypothesis on `o`. -/
theorem nech_interval_mono {n : ℕ} (G : List LGate)
    (hop : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : ∀ g ∈ G, g.inputs.length ≤ 2)
    (z y : Fin n → Bool) (hzy : z ≤ y) {ι : Type*} (T : Finset ι) (o : ι → ℕ)
    (S : ι → Finset (Fin n))
    (hdisj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → (S a ∩ S b).card ≤ 1)
    (ho : ∀ w ∈ T, ∀ x, z ≤ x → x ≤ y → val G x (o w) = Dag.orOf (S w) x)
    (hz : ∀ w ∈ T, Dag.orOf (S w) z = false) :
    ∑ w ∈ T, (((S w).filter fun i => y i = true).card - 1) ≤ G.length := by
  classical
  rw [← Finset.sum_filter_of_ne
    (p := fun w => 2 ≤ ((S w).filter fun i => y i = true).card) (fun w _ h => by omega)]
  set T' := T.filter fun w => 2 ≤ ((S w).filter fun i => y i = true).card with hT'
  let Sy : ι → Finset (Fin n) := fun w => (S w).filter fun i => y i = true
  have hmem : ∀ w ∈ T', w ∈ T ∧ 2 ≤ (Sy w).card := fun w hw => Finset.mem_filter.mp hw
  have hgw : ∀ w ∈ T', n ≤ o w ∧ o w < n + G.length := fun w hw =>
    gate_wire_of_two G z y hzy (o w) (S w) (ho w (hmem w hw).1) (hz w (hmem w hw).1)
      (hmem w hw).2
  rcases T'.eq_empty_or_nonempty with hT | ⟨w0, hw0⟩
  · rw [hT]; simp
  have hpos : 0 < n + G.length := by have := hgw w0 hw0; omega
  let D : Dag n G.length := ofList G G.length
  let E : Dag n G.length := D.restrict (downρ y)
  let o' : ι → Fin (n + G.length) := fun w =>
    if h : o w < n + G.length then ⟨o w, h⟩ else ⟨0, hpos⟩
  have ho' : ∀ w ∈ T', ∀ x, z ≤ x → E.val x (o' w) = Dag.orOf (Sy w) x := by
    intro w hw x hx
    obtain ⟨hn, hlt⟩ := hgw w hw
    have e : o' w = ⟨o w, hlt⟩ := by simp [o', hlt]
    rw [e, Dag.val_restrict_override _ _ _ _ fun j hj => by
      have := congrArg Fin.val hj
      simp at this
      omega]
    rw [override_downρ, ofList_val, ho w (hmem w hw).1 _ (le_inf hx hzy) inf_le_right, orOf_inf]
  refine E.sum_card_sub_one_le_andOr (fun j => ?_) (fun j => ?_) z T' o' Sy ?_ ho' ?_
  · show ((D.gate j).subst _).op = GateOp.and ∨ ((D.gate j).subst _).op = GateOp.or
    rw [KGate.subst_op, ofList_gate, conv_op]
    exact getD_ind (P := fun g => g.op = GateOp.and ∨ g.op = GateOp.or) hop (Or.inr rfl) j
  · show ((D.gate j).subst _).inputs.length ≤ 2
    simp only [KGate.subst, List.length_map]
    exact ofList_fanin G G.length hfan j
  · intro a ha b hb hab
    exact (Finset.card_le_card (Finset.inter_subset_inter (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))).trans (hdisj a (hmem a ha).1 b (hmem b hb).1 hab)
  · intro w hw
    have := hz w (hmem w hw).1
    simp only [Dag.orOf, decide_eq_false_iff_not, not_exists, not_and, Finset.mem_filter,
      Sy] at this ⊢
    exact fun v hv hzv => this v hv.1 hzv

/-! ## The two worlds -/

/-- Both worlds are AND/OR circuits of fan-in `≤ 2`. -/
theorem constNot_andOr {b : GateOp} (hb : b = GateOp.and ∨ b = GateOp.or) (gates : List LGate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ gates.map (L_meta_951_aux.constNot b),
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hm
  obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hop, hlen⟩ := hg g0 h0
  obtain ⟨op, ins⟩ := g0
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [L_meta_951_aux.constNot, hlen]

/-- **The Nechiporuk bound in one world, on an interval.** If the world `gates.map (constNot b)`
(`b = OR`: `C0`; `b = AND`: `C1`) agrees with the circuit at the outputs on `{z ≤ x ≤ y}`, then
`Σ_{w : S w ∩ z = ∅} (|S w ∩ y| − 1) ≤ gates.length`. Any number of NOT gates. -/
theorem nech_interval {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (bop : GateOp) (hb : bop = GateOp.and ∨ bop = GateOp.or) (z y : Fin n → Bool) (hzy : z ≤ y)
    (hC : ∀ x, z ≤ x → x ≤ y → ∀ w,
      val (gates.map (L_meta_951_aux.constNot bop)) x (out w) = val gates x (out w)) :
    ∑ w ∈ Finset.univ.filter (fun w => ∀ v ∈ S w, z v = false),
      (((S w).filter fun i => y i = true).card - 1) ≤ gates.length := by
  have h := nech_interval_mono (gates.map (L_meta_951_aux.constNot bop))
    (fun g hm => (constNot_andOr hb gates hg g hm).1)
    (fun g hm => (constNot_andOr hb gates hg g hm).2) z y hzy
    (Finset.univ.filter fun w => ∀ v ∈ S w, z v = false) out S
    (fun a _ b _ hab => hS a b hab) (fun w _ x hx hxy => (hC x hx hxy w).trans (hev w x))
    (fun w hw => by
      have hw' := (Finset.mem_filter.mp hw).2
      simp only [Dag.orOf, decide_eq_false_iff_not, not_exists, not_and]
      intro v hv hzv
      rw [hw' v hv] at hzv
      exact absurd hzv (by simp))
  rwa [List.length_map] at h

/-- **(1-pt) The lower world at a base point.** If `C0` (NOT := `0`) agrees with the circuit at
the outputs on the up-cube `{x ≥ z}`, the sets avoiding `z` cost
`Σ_{w : S w ∩ z = ∅} (|S w| − 1) ≤ gates.length`. -/
theorem nech_one_point {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (z : Fin n → Bool)
    (hC : ∀ x, z ≤ x → ∀ w, val (C0 gates) x (out w) = val gates x (out w)) :
    ∑ w ∈ Finset.univ.filter (fun w => ∀ v ∈ S w, z v = false), ((S w).card - 1) ≤
      gates.length := by
  have h := nech_interval S hS gates out hg hev GateOp.or (Or.inr rfl) z (fun _ => true)
    (fun j => Bool.le_true _) (fun x hx _ w => hC x hx w)
  simpa using h

/-- **(0-pt) The upper world at a top point.** If `C1` (NOT := `1`) agrees with the circuit at
the outputs on the down-cube `{x ≤ y}`, then `Σ_w (|S w ∩ y| − 1) ≤ gates.length`. -/
theorem nech_zero_point {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (y : Fin n → Bool)
    (hC : ∀ x, x ≤ y → ∀ w, val (C1 gates) x (out w) = val gates x (out w)) :
    ∑ w, (((S w).filter fun i => y i = true).card - 1) ≤ gates.length := by
  have h := nech_interval S hS gates out hg hev GateOp.and (Or.inl rfl) (fun _ => false) y
    (fun j => Bool.false_le _) (fun x _ hx w => hC x hx w)
  simpa using h

/-! ## From the value of the NOT gate to the world -/

/-- With at most one NOT, every gate before the NOT gate is AND/OR. -/
theorem take_andOr {gates : List LGate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (p : ℕ) (hp : p < gates.length)
    (hnot : (gates[p]'hp).op = GateOp.not) :
    ∀ g ∈ gates.take p, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  rw [List.getElem_take]
  have hip : i < p := by rw [List.length_take] at hi; omega
  rcases (hg _ (List.getElem_mem _)).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hU i p _ hp h hnot) (by omega)

/-- **The NOT gate is antitone** (its input is computed by the AND/OR prefix). -/
theorem not_val_anti {n : ℕ} {gates : List LGate}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (p : ℕ) (hp : p < gates.length)
    (hnot : (gates[p]'hp).op = GateOp.not) {x x' : Fin n → Bool} (hxx : x ≤ x') :
    val gates x' (n + p) = true → val gates x (n + p) = true := by
  rw [listVal_gate gates x' p hp, listVal_gate gates x p hp, hnot]
  have hm := mono_val_bridge (gates.take p) (take_andOr hg hU p hp hnot) x x'
    (fun c hc => le_antisymm (Bool.le_true _) (hc ▸ hxx c))
  cases hin : (gates[p]'hp).inputs with
  | nil => simp [GateOp.eval]
  | cons j r =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro h'
    cases hx : val (gates.take p) x j
    · rfl
    · rw [hm j hx] at h'; exact h'

/-- The kernel's NOT gates of `ofList gates` are the list's NOT gates. -/
theorem ofList_isNot {n : ℕ} (gates : List LGate) (i : Fin gates.length)
    (h : ((ofList gates gates.length : Dag n _).gate i).isNot = true) :
    (gates[i.1]'i.2).op = GateOp.not := by
  rw [KGate.isNot_iff, ofList_gate, conv_op, List.getD_eq_getElem _ _ i.2] at h
  exact h

/-- If every NOT gate has value `b` at `x`, the world `gates.map (constNot (bif b …))` agrees with
the circuit at `x` on every wire. -/
theorem world_agree {n : ℕ} (gates : List LGate) (x : Fin n → Bool) (b : Bool)
    (hall : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
      val gates x (n + p) = b) :
    ∀ i, val (if b then C1 gates else C0 gates) x i = val gates x i := by
  have hlen : (if b then C1 gates else C0 gates).length = gates.length := by
    cases b <;> simp [L_meta_951_aux.C0, L_meta_951_aux.C1]
  refine listVal_rel_of_dag gates _ hlen x x (fun a c => c = a) rfl fun w => ?_
  have e : (ofList (if b then C1 gates else C0 gates) gates.length : Dag n _) =
      (ofList gates gates.length).constNot b := by
    cases b
    · exact ofList_C0 gates _
    · exact ofList_C1 gates _
  rw [e]
  refine (ofList gates gates.length).val_constNot_of_eq b x (fun j hj => ?_) w
  rw [ofList_val]
  exact hall j.1 j.2 (ofList_isNot gates j hj)

/-- **NOT `= 0` at `z` puts the up-cube of `z` in the lower world.** With at most one NOT gate,
if every NOT gate is `false` at `z`, then `C0` agrees with the circuit on every wire at every
`x ≥ z`. -/
theorem C0_agree_of_not_false {n : ℕ} (gates : List LGate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (z : Fin n → Bool)
    (hz : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
      val gates z (n + p) = false) :
    ∀ x, z ≤ x → ∀ i, val (C0 gates) x i = val gates x i := by
  intro x hx
  have := world_agree gates x false fun p hp hnot => by
    cases h : val gates x (n + p)
    · rfl
    · have h' := not_val_anti hg hU p hp hnot hx h
      rw [hz p hp hnot] at h'
      exact absurd h' (by simp)
  simpa using this

/-- **NOT `= 1` at `y` puts the down-cube of `y` in the upper world.** With at most one NOT
gate, if every NOT gate is `true` at `y`, then `C1` agrees with the circuit on every wire at
every `x ≤ y`. -/
theorem C1_agree_of_not_true {n : ℕ} (gates : List LGate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates) (y : Fin n → Bool)
    (hy : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
      val gates y (n + p) = true) :
    ∀ x, x ≤ y → ∀ i, val (C1 gates) x i = val gates x i := by
  intro x hx
  have := world_agree gates x true fun p hp hnot =>
    not_val_anti hg hU p hp hnot hx (hy p hp hnot)
  simpa using this

/-! ## The bounds from the value of the NOT gate -/

/-- **(1-pt), one NOT, NOT `= 0` at `z`.** `Σ_{w : S w ∩ z = ∅} (|S w| − 1) ≤ gates.length`. -/
theorem nech_one_point_of_not {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (z : Fin n → Bool)
    (hz : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
      val gates z (n + p) = false) :
    ∑ w ∈ Finset.univ.filter (fun w => ∀ v ∈ S w, z v = false), ((S w).card - 1) ≤
      gates.length :=
  nech_one_point S hS gates out hg hev z fun x hx w =>
    C0_agree_of_not_false gates hg hU z hz x hx (out w)

/-- **(0-pt), one NOT, NOT `= 1` at `y`.** `Σ_w (|S w ∩ y| − 1) ≤ gates.length`. -/
theorem nech_zero_point_of_not {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (y : Fin n → Bool)
    (hy : ∀ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not →
      val gates y (n + p) = true) :
    ∑ w, (((S w).filter fun i => y i = true).card - 1) ≤ gates.length :=
  nech_zero_point S hS gates out hg hev y fun x hx w =>
    C1_agree_of_not_true gates hg hU y hy x hx (out w)

/-- **The two-world dichotomy at a point.** With at most one NOT gate, at every point `z` one of
the two bounds holds: the lower-world bound with base `z` (NOT `= 0` at `z`) or the upper-world
bound with top `z` (NOT `= 1` at `z`). -/
theorem nech_two_world {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (z : Fin n → Bool) :
    ∑ w ∈ Finset.univ.filter (fun w => ∀ v ∈ S w, z v = false), ((S w).card - 1) ≤
        gates.length ∨
      ∑ w, (((S w).filter fun i => z i = true).card - 1) ≤ gates.length := by
  by_cases h : ∃ (p : ℕ) (hp : p < gates.length), (gates[p]'hp).op = GateOp.not ∧
      val gates z (n + p) = true
  · obtain ⟨p, hp, hnot, hv⟩ := h
    refine Or.inr (nech_zero_point_of_not S hS gates out hg hU hev z fun q hq hq' => ?_)
    rw [hU q p hq hp hq' hnot]
    exact hv
  · refine Or.inl (nech_one_point_of_not S hS gates out hg hU hev z fun p hp hnot => ?_)
    cases hv : val gates z (n + p)
    · rfl
    · exact absurd ⟨p, hp, hnot, hv⟩ h

/-! ## PartialBound-style forms: the NOT gate reads the wire `hw` -/

/-- The NOT gate at `p` reading `hw` is the negation of `hw`. -/
theorem val_not_input {n : ℕ} (gates : List LGate) (p hw : ℕ) (hp : p < gates.length)
    (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩) (hwlt : hw < n + p) (x : Fin n → Bool) :
    val gates x (n + p) = !val gates x hw := by
  rw [listVal_gate gates x p hp, hnot]
  have h := L_meta_951_aux.val_append (gates.take p) (gates.drop p) x hw
    (by rw [List.length_take]; omega)
  rw [List.take_append_drop] at h
  simp [GateOp.eval, h]

theorem not_eq_of_input {n : ℕ} (gates : List LGate) (hU : AtMostOneNot gates) (p hw : ℕ)
    (hp : p < gates.length) (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩) (hwlt : hw < n + p)
    (x : Fin n → Bool) (b : Bool) (hx : val gates x hw = !b) :
    ∀ (q : ℕ) (hq : q < gates.length), (gates[q]'hq).op = GateOp.not →
      val gates x (n + q) = b := by
  intro q hq hq'
  rw [hU q p hq hp hq' (by rw [hnot]), val_not_input gates p hw hp hnot hwlt, hx, Bool.not_not]

/-- **(1-pt), the NOT gate at `p` reads `hw`, and `hw(z) = 1`.**
`Σ_{w : S w ∩ z = ∅} (|S w| − 1) ≤ gates.length`. -/
theorem nech_one_point_of_input {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (p hw : ℕ) (hp : p < gates.length) (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩)
    (hwlt : hw < n + p) (z : Fin n → Bool) (hz : val gates z hw = true) :
    ∑ w ∈ Finset.univ.filter (fun w => ∀ v ∈ S w, z v = false), ((S w).card - 1) ≤
      gates.length :=
  nech_one_point_of_not S hS gates out hg hU hev z
    (not_eq_of_input gates hU p hw hp hnot hwlt z false hz)

/-- **(0-pt), the NOT gate at `p` reads `hw`, and `hw(y) = 0`.**
`Σ_w (|S w ∩ y| − 1) ≤ gates.length`. -/
theorem nech_zero_point_of_input {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (p hw : ℕ) (hp : p < gates.length) (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩)
    (hwlt : hw < n + p) (y : Fin n → Bool) (hy : val gates y hw = false) :
    ∑ w, (((S w).filter fun i => y i = true).card - 1) ≤ gates.length :=
  nech_zero_point_of_not S hS gates out hg hU hev y
    (not_eq_of_input gates hU p hw hp hnot hwlt y true hy)

/-! ## Single-variable cases -/

/-- **One variable, lower world.** The NOT gate at `p` reads `hw`, and `hw` is on at the unit
vector `eof k`: the sets avoiding `k` cost `Σ_{k ∉ S w} (|S w| − 1) ≤ gates.length`. -/
theorem nech_one_point_single {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (p hw : ℕ) (hp : p < gates.length) (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩)
    (hwlt : hw < n + p) (k : Fin n) (hk : val gates (eof k) hw = true) :
    ∑ w ∈ Finset.univ.filter (fun w => k ∉ S w), ((S w).card - 1) ≤ gates.length := by
  have h := nech_one_point_of_input S hS gates out hg hU hev p hw hp hnot hwlt (eof k) hk
  have e : (Finset.univ.filter fun w => ∀ v ∈ S w, eof k v = false) =
      Finset.univ.filter fun w => k ∉ S w := by
    apply Finset.filter_congr
    intro w _
    simp only [L_meta_951_aux.eof, decide_eq_false_iff_not]
    constructor
    · intro h hk; exact h k hk rfl
    · rintro h v hv rfl; exact h hv
  rwa [e] at h

/-- **One variable, upper world.** The NOT gate at `p` reads `hw`, and `hw` is off at
`Zof {k}` (every variable but `k` on): `Σ_w (|S w \ {k}| − 1) ≤ gates.length`. -/
theorem nech_zero_point_single {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List LGate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hU : AtMostOneNot gates)
    (hev : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true))
    (p hw : ℕ) (hp : p < gates.length) (hnot : gates[p]'hp = ⟨GateOp.not, [hw]⟩)
    (hwlt : hw < n + p) (k : Fin n) (hk : val gates (Zof {k}) hw = false) :
    ∑ w, (((S w).erase k).card - 1) ≤ gates.length := by
  have h := nech_zero_point_of_input S hS gates out hg hU hev p hw hp hnot hwlt (Zof {k}) hk
  have e : ∀ w, ((S w).filter fun i => Zof {k} i = true) = (S w).erase k := by
    intro w
    ext i
    simp [L_meta_951_aux.Zof, and_comm]
  simpa only [e] using h

end PEqualNP.Kernel
