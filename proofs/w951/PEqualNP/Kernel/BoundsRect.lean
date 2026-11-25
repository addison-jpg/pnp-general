import PEqualNP.Kernel.W951TwoWorld
import PEqualNP.W951.PartialBound
import PEqualNP.Kernel.AndReplace
import PEqualNP.Base.Matching.Charging

section BoundsMap

/-!
# Kernel/BoundsMap: the multi-parameter bound interface for 951

Every lane of the 951 BOUNDS MAP reports a statement of one shape:

  on the instances satisfying `P`,   `base ≤ size + F`     (`BoundOn P F`),

where `F : Instance951 → ℕ` is a loss computed from the parameters of the instance (number of NOT
gates, cycle rank of the incidence hypergraph, weight of a star, ...). A strict gain
`base + G ≤ size` is `GainOn P G`. The full claim of 951 is `Target951 = BoundOn OneNot 0`.

* `Instance951`: `(n, m, S, gates, out)` with the hypotheses of 951 EXCEPT the bound on the number
  of NOT gates, which is the parameter `numNots` (axis A).
* parameters: `size`, `base`, `slack` (axis F), `numNots` (axis A), `incidence`, `cycleRank`,
  `Hyperforest` (axis B), `star` (axis C/F).
* algebra: `BoundOn.mono`, `.inf`, `.or`, `.and`, `.transport`, `boundOn_iff_slack`.
* proved instances: `boundOn_monotone` (k = 0, exact: Wegener Thm 6.2 through
  `sum_card_sub_one_le_length_andOr`), `boundOn_killVar` (`nech_one_point_single`, loss = star of
  `k`), `boundOn_coverVar` (`partial_bound`, loss = star of `k` minus 1).
* targets (Props, NOT proved here): `Target951`, `TargetNots`, `TargetCyc`, `TargetHyperforest`,
  `TargetHyperforestStrict`.
-/

namespace PEqualNP.Kernel.BoundsMap

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Outside
open PEqualNP.Outside.L_meta_951_aux (val AtMostOneNot eof)

/-- An instance of 951 with any number of NOT gates: the sets, the circuit and its output wires,
with the hypotheses of the problem (shapes of `IsCE`), without `AtMostOneNot` and without `hlt`. -/
structure Instance951 where
  n : ℕ
  m : ℕ
  S : Fin m → Finset (Fin n)
  gates : List LGate
  out : Fin m → ℕ
  h2 : ∀ i : Fin m, 2 ≤ (S i).card
  hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1
  hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
  hev : ∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)

namespace Instance951

variable (I : Instance951)

/-! ## Parameters -/

/-- The number of gates `s`. -/
def size : ℕ := I.gates.length

/-- `base = Σ_w (|S w| − 1)` (axis D). -/
def base : ℕ := ∑ w : Fin I.m, ((I.S w).card - 1)

/-- The slack `σ = base − s`, truncated at `0` (axis F). -/
def slack : ℕ := I.base - I.size

open Classical in
/-- The positions of the NOT gates. -/
noncomputable def notSet : Finset (Fin I.gates.length) :=
  Finset.univ.filter fun i => (I.gates[i.1]'i.2).op = GateOp.not

/-- The number `k` of NOT gates (axis A). -/
noncomputable def numNots : ℕ := I.notSet.card

/-- At most one NOT gate, in W951's form. -/
def OneNot : Prop := AtMostOneNot I.gates

/-- The incidence graph of the hypergraph: variables on the left, sets on the right. -/
def incidence : SimpleGraph (Fin I.n ⊕ Fin I.m) :=
  SimpleGraph.fromRel fun a b => ∃ v w, a = Sum.inl v ∧ b = Sum.inr w ∧ v ∈ I.S w

/-- The cycle rank `|E| − |V| + c` of the incidence graph (axis B): `|E| = Σ_w |S w|`,
`|V| = n + m`, `c` the number of connected components (isolated variables count on both sides). -/
noncomputable def cycleRank : ℕ :=
  (∑ w : Fin I.m, (I.S w).card) + Nat.card I.incidence.ConnectedComponent - (I.n + I.m)

/-- The hypergraph is a (Berge) hyperforest: its incidence graph has no cycle. -/
def Hyperforest : Prop := I.incidence.IsAcyclic

open Classical in
/-- The weight of the star of the variable `k`: `Σ_{w ∋ k} (|S w| − 1)`. -/
noncomputable def star (k : Fin I.n) : ℕ :=
  ∑ w ∈ Finset.univ.filter (fun w => k ∈ I.S w), ((I.S w).card - 1)

/-- **`KillVar k`**: the NOT gate sits at `p` and reads `hw`, and `hw` is on at the unit vector
`e_k` (e.g. `x_k` is a prime implicant of the NOT's input `h`). Axis C. -/
def KillVar (k : Fin I.n) : Prop :=
  ∃ (p hw : ℕ) (hp : p < I.gates.length), I.gates[p]'hp = ⟨GateOp.not, [hw]⟩ ∧ hw < I.n + p ∧
    val I.gates (eof k) hw = true

/-- **`CoverVar k`**: the only NOT gate sits at `p` and reads `hw`, and once `x_k = 1` the wire
`hw` is on wherever an output avoiding `k` is on (`h|_{x_k=1} ≥ o_w` for `w ∌ k`). Axis C. -/
def CoverVar (k : Fin I.n) : Prop :=
  ∃ (p hw : ℕ) (hp : p < I.gates.length), I.gates[p]'hp = ⟨GateOp.not, [hw]⟩ ∧ hw < I.n + p ∧
    (∀ (i : ℕ) (hi : i < I.gates.length), i ≠ p →
      (I.gates[i]'hi).op = GateOp.and ∨ (I.gates[i]'hi).op = GateOp.or) ∧
    ∀ w, k ∉ I.S w → ∀ x : Fin I.n → Bool, x k = true →
      val I.gates x (I.out w) = true → val I.gates x hw = true

theorem oneNot_iff : I.OneNot ↔ I.numNots ≤ 1 := by
  classical
  rw [numNots, Finset.card_le_one]
  constructor
  · intro h a ha b hb
    exact Fin.ext (h a.1 b.1 a.2 b.2 (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
  · intro h i1 i2 h1 h2 e1 e2
    exact congrArg Fin.val (h ⟨i1, h1⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e1⟩)
      ⟨i2, h2⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e2⟩))

theorem andOr_of_numNots_eq_zero (h : I.numNots = 0) :
    ∀ g ∈ I.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  classical
  intro g hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  rcases (I.hg _ (List.getElem_mem hi)).1 with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · have hmem : (⟨i, hi⟩ : Fin I.gates.length) ∈ I.notSet :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩
    rw [numNots, Finset.card_eq_zero] at h
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)

/-- Every output wire is a wire of the circuit. -/
theorem out_lt (w : Fin I.m) : I.out w < I.n + I.gates.length := by
  by_contra hlt
  have h0 := listVal_ge I.gates (fun _ : Fin I.n => true) (I.out w) (by omega)
  have h1 := I.hev w fun _ => true
  have hne : (I.S w).Nonempty := Finset.card_pos.mp (by have := I.h2 w; omega)
  obtain ⟨v, hv⟩ := hne
  rw [h0] at h1
  exact absurd h1.symm (by simpa using ⟨v, hv⟩)

/-- `base = Σ_{w ∌ k} (|S w| − 1) + star k`. -/
theorem base_eq_add_star (k : Fin I.n) :
    I.base = ∑ w ∈ Finset.univ.filter (fun w => k ∉ I.S w), ((I.S w).card - 1) + I.star k := by
  classical
  rw [base, star, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => k ∈ I.S w) _).symm

end Instance951

/-! ## The bound interface -/

/-- **A bound on the map.** On the instances satisfying `P`, `base ≤ size + F`. -/
def BoundOn (P : Instance951 → Prop) (F : Instance951 → ℕ) : Prop :=
  ∀ I, P I → I.base ≤ I.size + F I

/-- **A strict gain.** On the instances satisfying `P`, `base + G ≤ size`. -/
def GainOn (P : Instance951 → Prop) (G : Instance951 → ℕ) : Prop :=
  ∀ I, P I → I.base + G I ≤ I.size

variable {P P' Q : Instance951 → Prop} {F F' G : Instance951 → ℕ}

/-- A bound is a bound on the slack. -/
theorem boundOn_iff_slack : BoundOn P F ↔ ∀ I, P I → I.slack ≤ F I := by
  simp only [BoundOn, Instance951.slack]
  exact forall₂_congr fun I _ => by omega

/-- Smaller region, larger loss. -/
theorem BoundOn.mono (h : BoundOn P F) (hP : ∀ I, P' I → P I) (hF : ∀ I, P' I → F I ≤ F' I) :
    BoundOn P' F' := fun I hI => (h I (hP I hI)).trans (Nat.add_le_add_left (hF I hI) _)

/-- Two bounds on the same region: the smaller loss. -/
theorem BoundOn.inf (h : BoundOn P F) (h' : BoundOn P F') : BoundOn P fun I => min (F I) (F' I) :=
  fun I hI => by have := h I hI; have := h' I hI; dsimp only; omega

/-- Two bounds on two regions: on the overlap, the smaller loss. -/
theorem BoundOn.and (h : BoundOn P F) (h' : BoundOn Q F') :
    BoundOn (fun I => P I ∧ Q I) fun I => min (F I) (F' I) :=
  (h.mono (fun _ hI => hI.1) fun _ _ => le_rfl).inf (h'.mono (fun _ hI => hI.2) fun _ _ => le_rfl)

/-- Two bounds on two regions: on the union, the larger loss. -/
theorem BoundOn.or (h : BoundOn P F) (h' : BoundOn Q F') :
    BoundOn (fun I => P I ∨ Q I) fun I => max (F I) (F' I) := by
  rintro I (hI | hI)
  · have := h I hI; dsimp only; omega
  · have := h' I hI; dsimp only; omega

/-- A case split with one loss function: a cover of the region by proved regions. -/
theorem BoundOn.cases (h : BoundOn P F) (h' : BoundOn Q F) : BoundOn (fun I => P I ∨ Q I) F := by
  rintro I (hI | hI)
  exacts [h I hI, h' I hI]

/-- A bound with a pointwise budget: if for every instance in the region SOME lane proves
`base ≤ size + c` with `c ≤ F`, the region is bounded by `F`. -/
theorem BoundOn.of_exists (h : ∀ I, P I → ∃ c, I.base ≤ I.size + c ∧ c ≤ F I) : BoundOn P F :=
  fun I hI => by obtain ⟨c, h1, h2⟩ := h I hI; omega

/-- **Transport along a reduction** `r` (restriction of a variable, deletion of outputs, ...):
if `r` maps `P` into `P'` and loses at most `G` (`base I − size I ≤ base (r I) − size (r I) + G I`
in additive form), a bound on `P'` gives one on `P`. -/
theorem BoundOn.transport (h : BoundOn P' F) (r : Instance951 → Instance951)
    (hr : ∀ I, P I → P' (r I) ∧ I.base + (r I).size ≤ (r I).base + I.size + G I) :
    BoundOn P fun I => F (r I) + G I := fun I hI => by
  have := h (r I) (hr I hI).1
  have := (hr I hI).2
  dsimp only
  omega

/-- A gain is a bound with no loss. -/
theorem GainOn.boundOn (h : GainOn P G) : BoundOn P 0 := fun I hI => by
  have := h I hI
  simp only [Pi.zero_apply]
  omega

theorem GainOn.mono {G' : Instance951 → ℕ} (h : GainOn P G) (hP : ∀ I, P' I → P I)
    (hG : ∀ I, P' I → G' I ≤ G I) : GainOn P' G' := fun I hI => by
  have := h I (hP I hI); have := hG I hI; omega

/-! ## Proved instances -/

/-- **Axis A, `k = 0`, exact** (Nechiporuk; Wegener Thm 6.2 / Cor 6.1): a circuit without NOT
gates has `base ≤ size`. -/
theorem boundOn_monotone : BoundOn (fun I => I.numNots = 0) 0 := by
  intro I h
  simp only [Pi.zero_apply, add_zero]
  exact sum_card_sub_one_le_length_andOr I.gates (I.andOr_of_numNots_eq_zero h)
    (fun g hm => (I.hg g hm).2) (fun _ => false) Finset.univ I.out I.S
    (fun w _ => I.out_lt w) (fun a _ b _ hab => I.hS a b hab)
    (fun w _ x _ => I.hev w x) (fun w _ => by simp [Dag.orOf])

/-- **Axis C/F, pointwise** (`nech_one_point_single`): one NOT whose input is on at `e_k` saves at
most the star of `k`. -/
theorem Instance951.base_le_of_killVar (I : Instance951) (hU : I.OneNot) (k : Fin I.n) (hk : I.KillVar k) :
    I.base ≤ I.size + I.star k := by
  obtain ⟨p, hw, hp, hnot, hwlt, hv⟩ := hk
  have h := nech_one_point_single I.S I.hS I.gates I.out I.hg hU I.hev p hw hp hnot hwlt k hv
  rw [I.base_eq_add_star k]
  exact Nat.add_le_add_right h _

/-- **Axis C/F, pointwise** (`partial_bound`): if the NOT's input covers the outputs avoiding `k`
once `x_k = 1`, the NOT saves at most the star of `k` minus one. -/
theorem Instance951.base_le_of_coverVar (I : Instance951) (k : Fin I.n) (hk : I.CoverVar k) :
    I.base ≤ I.size + (I.star k - 1) := by
  obtain ⟨p, hw, hp, hnot, hwlt, hother, hc⟩ := hk
  have h := L_meta_951_aux.partial_bound I.S I.hS I.gates I.out I.hg I.hev p hw hp hnot hwlt
    hother k hc
  have e := I.base_eq_add_star k
  simp only [Instance951.size]
  omega

/-- `base_le_of_killVar` on the map: loss `F` wherever some killed variable has star `≤ F`
(e.g. `F = min_k star k` when the NOT's input is on at every unit vector). -/
theorem boundOn_killVar (F : Instance951 → ℕ) :
    BoundOn (fun I => I.OneNot ∧ ∃ k, I.KillVar k ∧ I.star k ≤ F I) F :=
  BoundOn.of_exists fun I ⟨hU, k, hk, hF⟩ => ⟨_, I.base_le_of_killVar hU k hk, hF⟩

/-- `base_le_of_coverVar` on the map: loss `F` wherever some covered variable has star `≤ F + 1`. -/
theorem boundOn_coverVar (F : Instance951 → ℕ) :
    BoundOn (fun I => ∃ k, I.CoverVar k ∧ I.star k - 1 ≤ F I) F :=
  BoundOn.of_exists fun I ⟨k, hk, hF⟩ => ⟨_, I.base_le_of_coverVar k hk, hF⟩

/-! ## Targets (statements only) -/

/-- **951**: one NOT gate saves nothing. Equivalent to `no_minCE` (`target951_iff`). -/
def Target951 : Prop := BoundOn Instance951.OneNot 0

/-- **Axis A**: `k` NOT gates save at most `F k`. -/
def TargetNots (F : ℕ → ℕ) : Prop := BoundOn (fun _ => True) fun I => F I.numNots

/-- **Axis B**: with one NOT, the saving is at most `F (cycle rank)`. -/
def TargetCyc (F : ℕ → ℕ) : Prop := BoundOn Instance951.OneNot fun I => F I.cycleRank

/-- **Axis B, `cyc = 0`**: 951 on hyperforests. -/
def TargetHyperforest : Prop := BoundOn (fun I => I.OneNot ∧ I.Hyperforest) 0

/-- **Axis B, `cyc = 0`, strict** (the board's Lemma J reading): on a hyperforest a circuit that
contains a NOT gate needs one gate more. -/
def TargetHyperforestStrict : Prop := GainOn (fun I => I.numNots = 1 ∧ I.Hyperforest) 1

/-- 951 in the unbundled form of `bound_of_noMinCE`. -/
theorem target951_iff : Target951 ↔
    ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)), (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List LGate) (out : Fin m → ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) → AtMostOneNot gates →
      (∀ (w : Fin m) (x : Fin n → Bool), val gates x (out w) = decide (∃ v ∈ S w, x v = true)) →
      ∑ i : Fin m, ((S i).card - 1) ≤ gates.length := by
  constructor
  · intro h n m S h2 hS gates out hg hU hev
    simpa [Instance951.base, Instance951.size] using h ⟨n, m, S, gates, out, h2, hS, hg, hev⟩ hU
  · intro h I hU
    simpa [Instance951.base, Instance951.size] using h I.S I.h2 I.hS I.gates I.out I.hg hU I.hev

/-- An axis-A bound with `F 0 = F 1 = 0` is 951. -/
theorem TargetNots.target951 {F : ℕ → ℕ} (h : TargetNots F) (h0 : F 0 = 0) (h1 : F 1 = 0) :
    Target951 := by
  refine BoundOn.mono h (fun _ _ => trivial) fun I hI => ?_
  have hk := I.oneNot_iff.mp hI
  have : I.numNots = 0 ∨ I.numNots = 1 := by omega
  rcases this with e | e <;> simp [e, h0, h1]

/-- An axis-B bound with `F = 0` everywhere on the cycle ranks that occur is 951. -/
theorem TargetCyc.target951 {F : ℕ → ℕ} (h : TargetCyc F) (hF : ∀ c, F c = 0) : Target951 :=
  BoundOn.mono h (fun _ hI => hI) fun I _ => by simp [hF]

/-- 951 gives every weaker axis statement. -/
theorem Target951.cyc (h : Target951) (F : ℕ → ℕ) : TargetCyc F :=
  BoundOn.mono h (fun _ hI => hI) fun _ _ => Nat.zero_le _

theorem Target951.hyperforest (h : Target951) : TargetHyperforest :=
  BoundOn.mono h (fun _ hI => hI.1) fun _ _ => le_rfl

/-- The strict hyperforest statement and the monotone bound give 951 on hyperforests. -/
theorem TargetHyperforestStrict.hyperforest (h : TargetHyperforestStrict) : TargetHyperforest := by
  intro I ⟨hU, hF⟩
  have hk := I.oneNot_iff.mp hU
  have : I.numNots = 0 ∨ I.numNots = 1 := by omega
  rcases this with e | e
  · exact boundOn_monotone I e
  · have := h I ⟨e, hF⟩
    simp only [Pi.zero_apply]
    omega

end PEqualNP.Kernel.BoundsMap

end BoundsMap

section Rectangle

/-!
# Kernel/Rectangle: per-gate semantic rectangles and the charging bound

Chistikov-style charging for a (lifted) monotone circuit, at a base point `z`. The outputs are
a finite family `o : ι → Fin (n + s)` of wires; an *entry* is a pair `(a, i) : ι × Fin n`
(output, input atom).

## The definition of the rectangle (and why)

* **Dependence.** `D.force g b` is `D` with gate `g` replaced by the constant `b`
  (`replaceGate` from `Kernel/AndReplace` with `KGate.const`). The wire `w` *depends on gate `g`
  at the input `x`* (`D.DepAt g x w`) if the two forcings give different values of `w` at `x`.
  This is the semantic notion "the value of `w` changes when the value of `g` changes": it is
  symmetric in the two constants, needs no monotonicity to state, implies that `g` is in the
  cone of `w` (`DepAt.reads`), and in a monotone dag it reads "forced to `0` the wire is off,
  forced to `1` it is on" (`depAt_iff`). The real circuit is one of the two forcings
  (`val_force_self`), so "forcing `g` changes `w`" is a special case (`depAt_of_ne`).
* **Rows.** `D.rows o z g`: the outputs `a` such that `o a` depends on `g` at some point of the
  cube `{x ≥ z}` (the cube `Kernel/Privacy` and Nechiporuk work on).
* **Columns.** `D.cols z g = D.supp z (gate g)`: the atoms off in `z` whose single flip turns
  the gate on from `z` (`Kernel/Privacy.supp`).
* **Rectangle.** `D.rect o z g = rows ×ˢ cols`, a genuine combinatorial rectangle in `ι × Fin n`.

The finer, non-product set `D.crit o z g` (*critical entries*: `i ∈ cols g` and `o a` depends
on `g` at the very point `z + e_i`) lies inside the rectangle (`crit_subset_rect`). Coverage is
proved for `crit`, hence for `rect`; the weight constraint is asked for `rect` (the weaker
conclusion needs the stronger hypothesis; `sum_mul_cover_le_size` takes any `R`, so `crit` or a
cone-based rectangle can be used instead).

## Results

* `sum_mul_cover_le_size`: any `R : Fin s → Finset ε`, `w ≥ 0`, `Σ_{e ∈ R g} w e ≤ 1` for all
  gates: `Σ_e w e · #{g | e ∈ R g} ≤ s`. With a coverage count: `sum_mul_le_size_of_le_cover`,
  `mul_sum_le_size_of_le_cover`.
* `sum_mul_cover_rect_le_size`, `sum_mul_le_size_of_le_cover_rect`: the instances for `rect`.
* Structural facts: `mem_crit_output` (a sensitive entry `(a, i)` of an output that is a gate
  wire is critical for that gate), `one_le_cover_rect`, and the resulting unconditional bound
  `sum_sens_le_size`.

**What is NOT proved (and is false in general):** coverage `≥ 2` of a sensitive entry by the
semantic rectangles. With redundancy (`o = h ∨ h'` with `h`, `h'` both on at `z + e_i`) no gate
other than the output gate is critical. A coverage count `c e` beyond `1` is therefore a
hypothesis of `sum_mul_le_size_of_le_cover_rect`, to be supplied by the application.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)
open PEqualNP.Base.Matching (cover)
open Function (update)

namespace Dag

variable {n s : ℕ}

/-! ## Forcing a gate -/

/-- Replacing gate `i` by a gate with the same value at `x` changes no wire value at `x`. -/
theorem val_replaceGate_of_eval (D : Dag n s) (i : Fin s) (g' : KGate (n + i))
    (x : Fin n → Bool)
    (h : (g'.eval fun a => D.val x (lift i a)) = (D.gate i).eval fun a => D.val x (lift i a)) :
    ∀ w, (D.replaceGate i g').val x w = D.val x w := by
  refine wire_induction (fun j => by simp) (fun j ih => ?_)
  by_cases hj : j = i
  · subst hj
    rw [val_replaceGate_self, h, val_natAdd]
  · rw [val_natAdd, val_natAdd, D.replaceGate_gate_of_ne _ _ hj]
    exact KGate.eval_congr fun a _ => ih a

/-- `D` with gate `g` forced to the constant `b`. -/
def force (D : Dag n s) (g : Fin s) (b : Bool) : Dag n s := D.replaceGate g (KGate.const b)

@[simp] theorem force_gate_self (D : Dag n s) (g : Fin s) (b : Bool) :
    (D.force g b).gate g = KGate.const b := replaceGate_gate_self _ _ _

theorem force_gate_of_ne (D : Dag n s) (g : Fin s) (b : Bool) {j : Fin s} (h : j ≠ g) :
    (D.force g b).gate j = D.gate j := replaceGate_gate_of_ne _ _ _ h

@[simp] theorem val_force_natAdd_self (D : Dag n s) (g : Fin s) (b : Bool) (x : Fin n → Bool) :
    (D.force g b).val x (Fin.natAdd n g) = b := by
  rw [force, val_replaceGate_self, KGate.eval_const]

/-- Wires below the forced gate keep their values. -/
theorem val_force_of_lt (D : Dag n s) (g : Fin s) (b : Bool) (x : Fin n → Bool)
    (w : Fin (n + s)) (hw : w.1 < n + g) : (D.force g b).val x w = D.val x w :=
  D.val_replaceGate_of_lt g _ x w hw

/-- Forcing a gate to its own value changes nothing: `D` is one of its two forcings. -/
theorem val_force_self (D : Dag n s) (g : Fin s) (x : Fin n → Bool) (w : Fin (n + s)) :
    (D.force g (D.val x (Fin.natAdd n g))).val x w = D.val x w :=
  D.val_replaceGate_of_eval g _ x (by rw [KGate.eval_const, val_natAdd]) w

theorem force_mono (D : Dag n s) (hD : D.Mono) (g : Fin s) (b : Bool) : (D.force g b).Mono := by
  intro j
  by_cases hj : j = g
  · subst hj
    rw [force_gate_self]
    exact KGate.opMono_const b
  · rw [D.force_gate_of_ne g b hj]
    exact hD j

/-- In a monotone dag, forcing a gate to `0` only lowers the wire values. -/
theorem val_force_false_le (D : Dag n s) (hD : D.Mono) (g : Fin s) (x : Fin n → Bool)
    (w : Fin (n + s)) : (D.force g false).val x w ≤ D.val x w := by
  refine val_le_val _ _ le_rfl (fun j v v' hv => ?_) w
  by_cases hj : j = g
  · subst hj
    rw [force_gate_self, KGate.eval_const]
    exact Bool.false_le _
  · rw [D.force_gate_of_ne g false hj]
    exact KGate.eval_mono (hD j) fun a _ => hv a

/-- In a monotone dag, forcing a gate to `1` only raises the wire values. -/
theorem val_le_force_true (D : Dag n s) (hD : D.Mono) (g : Fin s) (x : Fin n → Bool)
    (w : Fin (n + s)) : D.val x w ≤ (D.force g true).val x w := by
  refine val_le_val _ _ le_rfl (fun j v v' hv => ?_) w
  by_cases hj : j = g
  · subst hj
    rw [force_gate_self, KGate.eval_const]
    exact Bool.le_true _
  · rw [D.force_gate_of_ne g true hj]
    exact KGate.eval_mono (hD j) fun a _ => hv a

/-! ## Dependence of a wire on a gate -/

/-- The value of the wire `w` at the input `x` depends on the value of gate `g`: forcing `g` to
`false` and to `true` gives different values of `w`. -/
def DepAt (D : Dag n s) (g : Fin s) (x : Fin n → Bool) (w : Fin (n + s)) : Prop :=
  (D.force g false).val x w ≠ (D.force g true).val x w

instance (D : Dag n s) (g : Fin s) (x : Fin n → Bool) (w : Fin (n + s)) :
    Decidable (D.DepAt g x w) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- A gate depends on itself. -/
theorem depAt_self (D : Dag n s) (g : Fin s) (x : Fin n → Bool) :
    D.DepAt g x (Fin.natAdd n g) := by
  simp [DepAt]

/-- If some forcing of `g` changes the value of `w`, then `w` depends on `g`. -/
theorem depAt_of_ne (D : Dag n s) (g : Fin s) (x : Fin n → Bool) (w : Fin (n + s)) {b : Bool}
    (h : (D.force g b).val x w ≠ D.val x w) : D.DepAt g x w := by
  intro hd
  apply h
  have e := D.val_force_self g x w
  cases b <;> cases hc : D.val x (Fin.natAdd n g) <;> rw [hc] at e
  · exact e
  · rw [hd]; exact e
  · rw [← hd]; exact e
  · exact e

/-- **Monotone form.** In a monotone dag, `w` depends on `g` at `x` iff `w` is off with `g`
forced to `0` and on with `g` forced to `1`. -/
theorem depAt_iff (D : Dag n s) (hD : D.Mono) (g : Fin s) (x : Fin n → Bool)
    (w : Fin (n + s)) :
    D.DepAt g x w ↔ (D.force g false).val x w = false ∧ (D.force g true).val x w = true := by
  have h := (D.val_force_false_le hD g x w).trans (D.val_le_force_true hD g x w)
  unfold DepAt
  revert h
  cases (D.force g false).val x w <;> cases (D.force g true).val x w <;> decide

/-- Dependence is only possible above the gate. -/
theorem DepAt.le {D : Dag n s} {g : Fin s} {x : Fin n → Bool} {w : Fin (n + s)}
    (h : D.DepAt g x w) : n + g ≤ w.1 := by
  by_contra hlt
  exact h (by rw [D.val_force_of_lt g _ x w (by omega), D.val_force_of_lt g _ x w (by omega)])

/-- **Dependence implies reachability**: a wire that depends on gate `g` has `g` in its cone. -/
theorem DepAt.reads {D : Dag n s} {g : Fin s} {x : Fin n → Bool} {w : Fin (n + s)}
    (h : D.DepAt g x w) : Relation.ReflTransGen D.Reads w (Fin.natAdd n g) := by
  by_contra hw
  refine h (agree_off₂ (D.force g false) (D.force g true) x x
    (fun u => Relation.ReflTransGen D.Reads u (Fin.natAdd n g)) (fun _ _ => rfl)
    (fun j hj => ?_) w hw)
  have hjg : j ≠ g := by
    rintro rfl
    exact hj Relation.ReflTransGen.refl
  rw [D.force_gate_of_ne g _ hjg, D.force_gate_of_ne g _ hjg]
  exact ⟨rfl, fun a ha hbad => hj (Relation.ReflTransGen.head ⟨j, rfl, a, ha, rfl⟩ hbad)⟩

/-! ## The rectangle of a gate -/

section Rect

variable {ι : Type*} [Fintype ι]

open Classical in
/-- **Rows** of gate `g`: the outputs `a` whose wire `o a` depends on `g` somewhere on the cube
`{x ≥ z}`. -/
noncomputable def rows (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) (g : Fin s) :
    Finset ι :=
  Finset.univ.filter fun a => ∃ x, z ≤ x ∧ D.DepAt g x (o a)

/-- **Columns** of gate `g`: the atoms the gate is sensitive to at the base point `z`. -/
def cols (D : Dag n s) (z : Fin n → Bool) (g : Fin s) : Finset (Fin n) :=
  D.supp z (Fin.natAdd n g)

/-- **The semantic rectangle** of gate `g` at base `z`: `rows × cols`, a set of entries
(output, atom). -/
noncomputable def rect (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) (g : Fin s) :
    Finset (ι × Fin n) :=
  D.rows o z g ×ˢ D.cols z g

/-- **Critical entries** of gate `g`: `(a, i)` with `i` a column of `g` and `o a` depending on
`g` at the point `z + e_i`. -/
def crit (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) (g : Fin s) :
    Finset (ι × Fin n) :=
  Finset.univ.filter fun e => e.2 ∈ D.cols z g ∧ D.DepAt g (update z e.2 true) (o e.1)

/-- **Sensitive entries** at base `z`: `(a, i)` such that flipping atom `i` on switches the
output `o a` on. -/
def sens (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) : Finset (ι × Fin n) :=
  Finset.univ.filter fun e => e.2 ∈ D.supp z (o e.1)

theorem mem_rows {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {g : Fin s} {a : ι} :
    a ∈ D.rows o z g ↔ ∃ x, z ≤ x ∧ D.DepAt g x (o a) := by
  simp [rows]

theorem mem_rect {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {g : Fin s}
    {e : ι × Fin n} :
    e ∈ D.rect o z g ↔
      (∃ x, z ≤ x ∧ D.DepAt g x (o e.1)) ∧ e.2 ∈ D.supp z (Fin.natAdd n g) := by
  rw [rect, Finset.mem_product, mem_rows, cols]

theorem mem_crit {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {g : Fin s}
    {e : ι × Fin n} :
    e ∈ D.crit o z g ↔
      e.2 ∈ D.supp z (Fin.natAdd n g) ∧ D.DepAt g (update z e.2 true) (o e.1) := by
  unfold crit cols
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

theorem mem_sens {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {e : ι × Fin n} :
    e ∈ D.sens o z ↔ e.2 ∈ D.supp z (o e.1) := by
  simp [sens]

/-- The critical entries lie in the rectangle. -/
theorem crit_subset_rect (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) (g : Fin s) :
    D.crit o z g ⊆ D.rect o z g := by
  intro e he
  rw [mem_crit] at he
  exact mem_rect.mpr ⟨⟨_, le_update z e.2, he.2⟩, he.1⟩

/-- A row of gate `g` has `g` in its cone. -/
theorem reads_of_mem_rows {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {g : Fin s}
    {a : ι} (h : a ∈ D.rows o z g) : Relation.ReflTransGen D.Reads (o a) (Fin.natAdd n g) := by
  obtain ⟨x, -, hx⟩ := mem_rows.mp h
  exact hx.reads

/-- **Coverage by the output gate.** If the output `o a` is the wire of gate `g`, every sensitive
entry `(a, i)` is critical for `g`. -/
theorem mem_crit_output {D : Dag n s} {o : ι → Fin (n + s)} {z : Fin n → Bool} {g : Fin s}
    {e : ι × Fin n} (hg : o e.1 = Fin.natAdd n g) (he : e ∈ D.sens o z) : e ∈ D.crit o z g := by
  rw [mem_sens, hg] at he
  rw [mem_crit, hg]
  exact ⟨he, D.depAt_self g _⟩

/-- A critical entry in a monotone dag, read on the real circuit: gate `g` switches on from `z`
to `z + e_i`, and switching it off at `z + e_i` switches the output off. -/
theorem mem_crit_iff (D : Dag n s) (hD : D.Mono) {o : ι → Fin (n + s)} {z : Fin n → Bool}
    {g : Fin s} {e : ι × Fin n} :
    e ∈ D.crit o z g ↔
      e.2 ∈ D.supp z (Fin.natAdd n g) ∧ D.val (update z e.2 true) (o e.1) = true ∧
        (D.force g false).val (update z e.2 true) (o e.1) = false := by
  rw [mem_crit, depAt_iff D hD]
  refine and_congr_right fun hs => ?_
  have hon : D.val (update z e.2 true) (Fin.natAdd n g) = true := (mem_supp.mp hs).2.1
  have hv := D.val_force_self g (update z e.2 true) (o e.1)
  rw [hon] at hv
  rw [hv, and_comm]

/-- A sensitive entry always belongs to an output that is a gate wire or to the input wire of
its own atom. -/
theorem sens_cases (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool) {e : ι × Fin n}
    (he : e ∈ D.sens o z) : (∃ g, o e.1 = Fin.natAdd n g) ∨ o e.1 = Fin.castAdd s e.2 := by
  rw [mem_sens] at he
  induction h : o e.1 using Fin.addCases with
  | left j =>
    rw [h] at he
    exact Or.inr (by rw [Finset.mem_singleton.mp (D.supp_castAdd_subset z j he)])
  | right g => exact Or.inl ⟨g, rfl⟩

/-- The regrouping identity for the rectangles:
`Σ_g w(rect g) = Σ_e w e · #{g | e ∈ rect g}`. -/
theorem sum_rect_eq_sum_mul_cover [DecidableEq ι] {M : Type*} [CommSemiring M] (D : Dag n s)
    (o : ι → Fin (n + s)) (z : Fin n → Bool) (w : ι × Fin n → M) :
    ∑ g, ∑ e ∈ D.rect o z g, w e = ∑ e, w e * cover Finset.univ (D.rect o z) e :=
  Base.Matching.sum_sum_eq_sum_mul_cover_univ Finset.univ (D.rect o z) w

/-! ## The charging bound -/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Charging bound for a dag, any family of entry sets.** For `R : gates → Finset entries` and
nonnegative weights with `Σ_{e ∈ R g} w e ≤ 1` at every gate:
`Σ_e w e · #{g | e ∈ R g} ≤ s`. -/
theorem sum_mul_cover_le_size {ε : Type*} [DecidableEq ε] (_D : Dag n s) (R : Fin s → Finset ε)
    (w : ε → K) (hw : ∀ e, 0 ≤ w e) (hR : ∀ g, ∑ e ∈ R g, w e ≤ 1) (S : Finset ε) :
    ∑ e ∈ S, w e * cover Finset.univ R e ≤ s := by
  simpa using Base.Matching.sum_mul_cover_le_card Finset.univ R w hw (fun g _ => hR g) S

/-- The same with a coverage count `c e ≤ #{g | e ∈ R g}` on `S`. -/
theorem sum_mul_le_size_of_le_cover {ε : Type*} [DecidableEq ε] (_D : Dag n s)
    (R : Fin s → Finset ε) (w : ε → K) (hw : ∀ e, 0 ≤ w e) (hR : ∀ g, ∑ e ∈ R g, w e ≤ 1)
    (S : Finset ε) (c : ε → ℕ) (hc : ∀ e ∈ S, c e ≤ cover Finset.univ R e) :
    ∑ e ∈ S, w e * c e ≤ s := by
  simpa using Base.Matching.sum_mul_le_card_of_le_cover_nat Finset.univ R w hw
    (fun g _ => hR g) S c hc

/-- Uniform coverage `m` on the support of `w` in `S`: `m · Σ_{e ∈ S} w e ≤ s`. -/
theorem mul_sum_le_size_of_le_cover {ε : Type*} [DecidableEq ε] (_D : Dag n s)
    (R : Fin s → Finset ε) (w : ε → K) (hw : ∀ e, 0 ≤ w e) (hR : ∀ g, ∑ e ∈ R g, w e ≤ 1)
    (S : Finset ε) (m : ℕ) (hm : ∀ e ∈ S, w e ≠ 0 → m ≤ cover Finset.univ R e) :
    (m : K) * ∑ e ∈ S, w e ≤ s := by
  simpa using Base.Matching.mul_sum_le_card_of_le_cover Finset.univ R w hw
    (fun g _ => hR g) S m hm

variable [DecidableEq ι]

/-- **Instantiation (the request).** Weights `w ≥ 0` on entries with `w(rect g) ≤ 1` for every
gate: `Σ_e w e · #{g | e ∈ rect g} ≤ s`. -/
theorem sum_mul_cover_rect_le_size (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool)
    (w : ι × Fin n → K) (hw : ∀ e, 0 ≤ w e) (hR : ∀ g, ∑ e ∈ D.rect o z g, w e ≤ 1) :
    ∑ e, w e * cover Finset.univ (D.rect o z) e ≤ s :=
  D.sum_mul_cover_le_size (D.rect o z) w hw hR Finset.univ

/-- **Instantiation with a coverage count.** If every entry `e ∈ S` lies in at least `c e`
rectangles (hypothesis: only `c = 1` on sensitive entries is generic, `one_le_cover_rect`), then
`Σ_{e ∈ S} w e · c e ≤ s`. -/
theorem sum_mul_le_size_of_le_cover_rect (D : Dag n s) (o : ι → Fin (n + s))
    (z : Fin n → Bool) (w : ι × Fin n → K) (hw : ∀ e, 0 ≤ w e)
    (hR : ∀ g, ∑ e ∈ D.rect o z g, w e ≤ 1) (S : Finset (ι × Fin n)) (c : ι × Fin n → ℕ)
    (hc : ∀ e ∈ S, c e ≤ cover Finset.univ (D.rect o z) e) : ∑ e ∈ S, w e * c e ≤ s :=
  D.sum_mul_le_size_of_le_cover (D.rect o z) w hw hR S c hc

/-- Coverage transfers from the critical entries to the rectangles. -/
theorem cover_crit_le_cover_rect (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool)
    (e : ι × Fin n) : cover Finset.univ (D.crit o z) e ≤ cover Finset.univ (D.rect o z) e :=
  Base.Matching.cover_mono (fun g _ => D.crit_subset_rect o z g) e

/-- **Generic coverage.** A sensitive entry of an output that is a gate wire lies in at least one
rectangle (that of the output gate). -/
theorem one_le_cover_rect (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool)
    {e : ι × Fin n} {g : Fin s} (hg : o e.1 = Fin.natAdd n g) (he : e ∈ D.sens o z) :
    1 ≤ cover Finset.univ (D.rect o z) e :=
  Base.Matching.cover_pos_iff.mpr
    ⟨g, Finset.mem_univ _, D.crit_subset_rect o z g (mem_crit_output hg he)⟩

/-- **Unconditional bound from coverage one.** If all outputs are gate wires, the total weight
of the sensitive entries is at most the number of gates. -/
theorem sum_sens_le_size (D : Dag n s) (o : ι → Fin (n + s)) (z : Fin n → Bool)
    (ho : ∀ a, ∃ g, o a = Fin.natAdd n g) (w : ι × Fin n → K) (hw : ∀ e, 0 ≤ w e)
    (hR : ∀ g, ∑ e ∈ D.rect o z g, w e ≤ 1) : ∑ e ∈ D.sens o z, w e ≤ s := by
  have h := D.sum_mul_le_size_of_le_cover_rect o z w hw hR (D.sens o z) (fun _ => 1)
    fun e he => by
      obtain ⟨g, hg⟩ := ho e.1
      exact D.one_le_cover_rect o z hg he
  simpa using h

end Rect

end Dag

end PEqualNP.Kernel

end Rectangle
