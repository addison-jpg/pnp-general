import PEqualNP.Kernel.W951TwoWorld
import PEqualNP.W951.PartialBound

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
