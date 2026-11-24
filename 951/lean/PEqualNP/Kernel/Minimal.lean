import PEqualNP.Kernel.Circuit

/-!
# Kernel/Minimal: the two minimality operations, with exact gate counts

Two operations a minimum-size circuit must survive, as general passes on `Dag n s`:

* **Compaction** `Dag.keep K` (`K : Finset (Fin s)` a set of gate indices): keep the gates in
  `K`, reindexed in order (`kemb K : Fin K.card → Fin s`, strictly monotone, range `K`), every
  read rewired through the order embedding. The result is a `Dag n K.card`: the size is `K.card`
  BY TYPE. If `K` is closed under reads (`GClosed`), every kept wire keeps its value
  (`val_keep`). The pass is total (a read of a dropped gate becomes the constant `false`; by
  closedness this never happens on kept gates).
* **Output deletion** `restrictOutputs O := keep (coneGates O)`: keep exactly the gates in the
  cone of the outputs `O`. Every output keeps its value (`val_restrictOutputs`), and
  `#coneGates O + #(gates outside every cone of O) = s` (`card_coneGates_add`); a closed set of
  gates containing the output gates contains the cone (`coneGates_subset`).
* **Restriction to a set of inputs** `simplify A O` (`A : (Fin n → Bool) → Prop`, e.g.
  `{x | x v = b}`, see `restrictVar`): (1) `prop A` replaces each gate that is constant on `A` by
  that constant, and each read by its representative on `A` (the constant, or the FIRST wire
  equal to it on `A`); then the gate is `prune`d (AND/OR/NOT absorb constant inputs); (2) keep
  the cone of the (representatives of the) non-constant outputs. On `A` every output is either
  constant or kept with its value (`val_simplify`); the size is exactly `s − #deadGates`
  (`card_simplify`), and every gate that is constant on `A` or a copy of an earlier wire on `A`
  is dead (`mem_deadGates_of_constOrCopy`). Gate-level criteria for N2/N3-type counts:
  a gate reading only constants is constant (`isConst_of_reads`); a fan-in ≤ 2 AND/OR gate
  reading a constant wire, and a NOT gate whose first input is constant, are dead
  (`mem_deadGates_of_effReads`); hence `#effective readers of x_v ≤ #dead(x_v := b)`
  (`card_readers_le`).
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)

/-! ## Rewiring a gate through a map to inputs -/

namespace Src

variable {k k' : ℕ}

/-- Replace each wire by an input of another gate (a wire or a constant). -/
def bind (f : Fin k → Src k') : Src k → Src k'
  | wire a => f a
  | const b => const b

@[simp] theorem eval_bind (f : Fin k → Src k') (s : Src k) (v : Fin k' → Bool) :
    (s.bind f).eval v = s.eval (fun a => (f a).eval v) := by cases s <;> rfl

end Src

namespace KGate

variable {k k' : ℕ}

/-- Rewire a gate: each input wire `a` becomes the input `f a`. Same operation, same arity. -/
def bind (f : Fin k → Src k') (g : KGate k) : KGate k' := ⟨g.op, g.inputs.map (Src.bind f)⟩

@[simp] theorem bind_op (f : Fin k → Src k') (g : KGate k) : (g.bind f).op = g.op := rfl

@[simp] theorem bind_inputs_length (f : Fin k → Src k') (g : KGate k) :
    (g.bind f).inputs.length = g.inputs.length := by simp [bind]

theorem eval_bind (f : Fin k → Src k') (g : KGate k) (v : Fin k' → Bool) :
    (g.bind f).eval v = g.eval (fun a => (f a).eval v) := by
  simp only [eval, bind, List.map_map]
  congr 1
  exact List.map_congr_left fun s _ => Src.eval_bind f s v

theorem mem_reads_bind {f : Fin k → Src k'} {g : KGate k} {a : Fin k'}
    (h : a ∈ (g.bind f).reads) : ∃ a' ∈ g.reads, f a' = Src.wire a := by
  rw [mem_reads] at h
  obtain ⟨t, ht, hta⟩ := List.mem_map.mp h
  cases t with
  | const b => simp [Src.bind] at hta
  | wire a' => exact ⟨a', mem_reads.mpr ht, hta⟩

/-- Absorb constant inputs where the operation allows it: AND drops `true` inputs and is `false`
with a `false` input; OR dually; NOT keeps only its first input, and is a constant if that
input is. MOD and MAJ gates are unchanged. The value never changes (`eval_prune`). -/
def prune : KGate k → KGate k
  | ⟨GateOp.and, ins⟩ =>
    if Src.const false ∈ ins then const false else ⟨GateOp.and, ins.filter (· != Src.const true)⟩
  | ⟨GateOp.or, ins⟩ =>
    if Src.const true ∈ ins then const true else ⟨GateOp.or, ins.filter (· != Src.const false)⟩
  | ⟨GateOp.not, []⟩ => ⟨GateOp.not, []⟩
  | ⟨GateOp.not, Src.const c :: _⟩ => const (!c)
  | ⟨GateOp.not, Src.wire a :: _⟩ => ⟨GateOp.not, [Src.wire a]⟩
  | ⟨GateOp.mod m, ins⟩ => ⟨GateOp.mod m, ins⟩
  | ⟨GateOp.maj, ins⟩ => ⟨GateOp.maj, ins⟩

theorem eval_prune (g : KGate k) (v : Fin k → Bool) : g.prune.eval v = g.eval v := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    simp only [prune]
    split_ifs with h
    · rw [eval_const]
      simp only [eval, GateOp.eval]
      symm
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      exact absurd (hall false (List.mem_map.mpr ⟨_, h, rfl⟩)) (by simp)
    · simp only [eval, GateOp.eval]
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      simp only [List.mem_map, List.mem_filter, id, forall_exists_index, and_imp]
      constructor
      · rintro hall b t ht rfl
        by_cases e : t = Src.const true
        · subst e; rfl
        · exact hall _ t ht (by simpa using e) rfl
      · rintro hall b t ht _ rfl
        exact hall _ t ht rfl
  | or =>
    simp only [prune]
    split_ifs with h
    · rw [eval_const]
      simp only [eval, GateOp.eval]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨_, h, rfl⟩, rfl⟩
    · simp only [eval, GateOp.eval]
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      simp only [List.mem_map, List.mem_filter, id]
      constructor
      · rintro ⟨b, ⟨t, ⟨ht, _⟩, rfl⟩, hb⟩
        exact ⟨_, ⟨t, ht, rfl⟩, hb⟩
      · rintro ⟨b, ⟨t, ht, rfl⟩, hb⟩
        refine ⟨_, ⟨t, ⟨ht, ?_⟩, rfl⟩, hb⟩
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        simp at hb
  | not =>
    rcases ins with _ | ⟨t, ins⟩
    · rfl
    · cases t with
      | const c => cases c <;> rfl
      | wire a => simp [prune, eval, GateOp.eval]
  | mod m => rfl
  | maj => rfl

theorem mem_reads_prune {g : KGate k} {a : Fin k} (h : a ∈ g.prune.reads) : a ∈ g.reads := by
  obtain ⟨op, ins⟩ := g
  rw [mem_reads] at h ⊢
  cases op with
  | and =>
    simp only [prune] at h
    split_ifs at h
    · simp [const] at h
    · exact (List.mem_filter.mp h).1
  | or =>
    simp only [prune] at h
    split_ifs at h
    · simp [const] at h
    · exact (List.mem_filter.mp h).1
  | not =>
    rcases ins with _ | ⟨t, ins⟩
    · exact h
    · cases t with
      | const c => simp [prune, const] at h
      | wire b =>
        simp only [prune, List.mem_singleton] at h
        rw [h]; exact List.mem_cons_self
  | mod m => exact h
  | maj => exact h

theorem prune_inputs_length (g : KGate k) : g.prune.inputs.length ≤ g.inputs.length := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    simp only [prune]; split_ifs
    · simp [const]
    · exact List.length_filter_le _ _
  | or =>
    simp only [prune]; split_ifs
    · simp [const]
    · exact List.length_filter_le _ _
  | not =>
    rcases ins with _ | ⟨t, ins⟩
    · exact le_rfl
    · cases t <;> simp [prune, const]
  | mod m => exact le_rfl
  | maj => exact le_rfl

/-- `prune` keeps the operation, or produces a constant gate (AND/OR with no input). -/
theorem prune_op (g : KGate k) :
    g.prune.op = g.op ∨
      (g.prune.inputs = [] ∧ (g.prune.op = GateOp.and ∨ g.prune.op = GateOp.or)) := by
  have hc : ∀ b : Bool, ((const b : KGate k).inputs = [] ∧
      ((const b : KGate k).op = GateOp.and ∨ (const b : KGate k).op = GateOp.or)) := by
    intro b; cases b <;> simp [const]
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => simp only [prune]; split_ifs; exacts [Or.inr (hc _), Or.inl rfl]
  | or => simp only [prune]; split_ifs; exacts [Or.inr (hc _), Or.inl rfl]
  | not =>
    rcases ins with _ | ⟨t, ins⟩
    · exact Or.inl rfl
    · cases t
      · exact Or.inl rfl
      · exact Or.inr (hc _)
  | mod m => exact Or.inl rfl
  | maj => exact Or.inl rfl

/-- After `prune`, an AND/OR/NOT gate has no constant-`true` input (so it is a W951 list gate). -/
theorem const_true_not_mem_prune (g : KGate k)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    Src.const true ∉ g.prune.inputs := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    simp only [prune]; split_ifs
    · simp [const]
    · simp [List.mem_filter]
  | or =>
    simp only [prune]; split_ifs with h
    · simp [const]
    · intro hm; exact h (List.mem_filter.mp hm).1
  | not =>
    rcases ins with _ | ⟨t, ins⟩
    · simp [prune]
    · cases t <;> simp [prune, const]
  | mod m => simp at hop
  | maj => simp at hop

end KGate

/-! ## Compaction: keep a set of gates, reindexed in order -/

namespace Dag

variable {n s : ℕ}

/-- The `t`-th gate of `K` (in increasing order). -/
def kemb (K : Finset (Fin s)) (t : Fin K.card) : Fin s := (K.orderIsoOfFin rfl t).1

theorem kemb_mem (K : Finset (Fin s)) (t : Fin K.card) : kemb K t ∈ K :=
  (K.orderIsoOfFin rfl t).2

theorem kemb_strictMono (K : Finset (Fin s)) : StrictMono (kemb K) :=
  fun _ _ h => (K.orderIsoOfFin rfl).strictMono h

/-- The position of a gate of `K` in `K`. -/
def krank (K : Finset (Fin s)) (j : Fin s) (hj : j ∈ K) : Fin K.card :=
  (K.orderIsoOfFin rfl).symm ⟨j, hj⟩

@[simp] theorem kemb_krank (K : Finset (Fin s)) (j : Fin s) (hj : j ∈ K) :
    kemb K (krank K j hj) = j := by
  simp [kemb, krank]

theorem krank_lt (K : Finset (Fin s)) {j : Fin s} (hj : j ∈ K) {t : Fin K.card}
    (h : j < kemb K t) : krank K j hj < t := by
  rw [← (kemb_strictMono K).lt_iff_lt, kemb_krank]; exact h

/-- The wires of gate indices in `K` (input wires are always in). -/
def gw (K : Finset (Fin s)) (w : Fin (n + s)) : Prop :=
  ∀ h : n ≤ w.1, (⟨w.1 - n, by omega⟩ : Fin s) ∈ K

theorem gw_natAdd {K : Finset (Fin s)} {i : Fin s} : gw (n := n) K (Fin.natAdd n i) ↔ i ∈ K := by
  constructor
  · intro h; have := h (by simp); simpa using this
  · intro h _; simpa using h

theorem gw_castAdd (K : Finset (Fin s)) (j : Fin n) : gw K (Fin.castAdd s j) :=
  fun h => absurd h (by simp)

/-- A set of gate indices closed under reads: a gate of `K` reads only inputs and gates of `K`. -/
def GClosed (D : Dag n s) (K : Finset (Fin s)) : Prop := D.Closed (gw K)

/-- Rewire one read of the `t`-th kept gate: an input stays, a kept gate is renumbered, a
dropped gate becomes the constant `false` (impossible under closedness). -/
def kw (K : Finset (Fin s)) (t : Fin K.card) (a : Fin (n + kemb K t)) : Src (n + t) :=
  if h : a.1 < n then Src.wire ⟨a.1, by omega⟩
  else if hj : (⟨a.1 - n, by omega⟩ : Fin s) ∈ K then
    Src.wire ⟨n + krank K _ hj, by
      have := krank_lt K hj (t := t) (by rw [Fin.lt_def]; simp; omega)
      rw [Fin.lt_def] at this; omega⟩
  else Src.const false

/-- **Compaction.** Keep the gates of `K`, in order. Size `K.card`, by type. -/
def keep (D : Dag n s) (K : Finset (Fin s)) : Dag n K.card :=
  ⟨fun t => (D.gate (kemb K t)).bind (kw K t)⟩

@[simp] theorem keep_gate (D : Dag n s) (K : Finset (Fin s)) (t : Fin K.card) :
    (D.keep K).gate t = (D.gate (kemb K t)).bind (kw K t) := rfl

@[simp] theorem keep_gate_op (D : Dag n s) (K : Finset (Fin s)) (t : Fin K.card) :
    ((D.keep K).gate t).op = (D.gate (kemb K t)).op := rfl

@[simp] theorem keep_gate_inputs_length (D : Dag n s) (K : Finset (Fin s)) (t : Fin K.card) :
    ((D.keep K).gate t).inputs.length = (D.gate (kemb K t)).inputs.length := by simp

/-- Compaction introduces no constant `true` input. -/
theorem keep_const_true (D : Dag n s) (K : Finset (Fin s)) (t : Fin K.card)
    (h : Src.const true ∉ (D.gate (kemb K t)).inputs) :
    Src.const true ∉ ((D.keep K).gate t).inputs := by
  intro hm
  simp only [keep_gate, KGate.bind, List.mem_map] at hm
  obtain ⟨u, hu, he⟩ := hm
  cases u with
  | const b =>
    cases b
    · simp [Src.bind] at he
    · exact h hu
  | wire a =>
    simp only [Src.bind, kw] at he
    split_ifs at he
    simp at he

/-- The wire of the original dag that a wire of the compacted dag stands for. -/
def ew (K : Finset (Fin s)) (w : Fin (n + K.card)) : Fin (n + s) :=
  if h : w.1 < n then ⟨w.1, by omega⟩
  else ⟨n + kemb K ⟨w.1 - n, by omega⟩, by have := (kemb K ⟨w.1 - n, by omega⟩).2; omega⟩

@[simp] theorem ew_castAdd (K : Finset (Fin s)) (j : Fin n) :
    ew K (Fin.castAdd K.card j) = Fin.castAdd s j := by
  simp [ew, Fin.ext_iff]

@[simp] theorem ew_natAdd (K : Finset (Fin s)) (t : Fin K.card) :
    ew K (Fin.natAdd n t) = Fin.natAdd n (kemb K t) := by
  simp [ew, Fin.ext_iff]

/-- **Compaction preserves values.** On a read-closed set of gates, every wire of the compacted
dag carries the value of the wire it stands for. -/
theorem val_keep (D : Dag n s) (K : Finset (Fin s)) (hK : D.GClosed K) (x : Fin n → Bool) :
    ∀ w, (D.keep K).val x w = D.val x (ew K w) := by
  refine wire_induction (fun j => by simp) (fun t ih => ?_)
  rw [val_natAdd, keep_gate, KGate.eval_bind, ew_natAdd, val_natAdd]
  apply KGate.eval_congr
  intro a ha
  have hcl := hK (kemb K t) (gw_natAdd.mpr (kemb_mem K t)) a ha
  unfold kw
  split_ifs with h hj
  · rw [Src.eval_wire, ih]
    congr 1
    simp [ew, lift, h]
  · rw [Src.eval_wire, ih]
    congr 1
    have e1 : lift t (⟨n + krank K _ hj, by
        have := krank_lt K hj (t := t) (by rw [Fin.lt_def]; simp; omega)
        rw [Fin.lt_def] at this; omega⟩ : Fin (n + t)) =
        Fin.natAdd n (krank K _ hj) := Fin.ext rfl
    rw [e1, ew_natAdd, kemb_krank]
    ext; simp; omega
  · exact absurd (hcl (by simp at h ⊢; omega)) (by simpa using hj)

/-- Every input wire, and every wire of a kept gate, is represented in the compacted dag. -/
theorem exists_ew (K : Finset (Fin s)) (w : Fin (n + s)) (hw : gw K w) :
    ∃ w' : Fin (n + K.card), ew K w' = w := by
  by_cases h : w.1 < n
  · exact ⟨Fin.castAdd _ ⟨w.1, h⟩, by rw [ew_castAdd]; exact Fin.ext rfl⟩
  · have hj := hw (by omega)
    refine ⟨Fin.natAdd n (krank K _ hj), ?_⟩
    rw [ew_natAdd, kemb_krank]
    ext; simp; omega

/-- A read of a compacted gate is (through `ew`) a read of the original gate. -/
theorem mem_reads_keep {D : Dag n s} {K : Finset (Fin s)} {t : Fin K.card} {a : Fin (n + t)}
    (ha : a ∈ ((D.keep K).gate t).reads) :
    ∃ a' ∈ (D.gate (kemb K t)).reads, ew K (lift t a) = lift (kemb K t) a' := by
  obtain ⟨a', ha', hk⟩ := KGate.mem_reads_bind ha
  refine ⟨a', ha', ?_⟩
  unfold kw at hk
  split_ifs at hk with h hj
  · injection hk with hk
    subst hk
    simp [ew, lift, h]
  · injection hk with hk
    subst hk
    have e1 : lift t (⟨n + krank K _ hj, by
        have := krank_lt K hj (t := t) (by rw [Fin.lt_def]; simp; omega)
        rw [Fin.lt_def] at this; omega⟩ : Fin (n + t)) =
        Fin.natAdd n (krank K _ hj) := Fin.ext rfl
    rw [e1, ew_natAdd, kemb_krank]
    ext; simp; omega

/-! ## Output deletion -/

/-- The gates in the cone of the wires `O`. -/
noncomputable def coneGates (D : Dag n s) (O : Fin (n + s) → Prop) : Finset (Fin s) := by
  classical exact Finset.univ.filter fun i => D.cone O (Fin.natAdd n i)

theorem mem_coneGates {D : Dag n s} {O : Fin (n + s) → Prop} {i : Fin s} :
    i ∈ D.coneGates O ↔ D.cone O (Fin.natAdd n i) := by
  classical simp [coneGates]

theorem gw_coneGates {D : Dag n s} {O : Fin (n + s) → Prop} {w : Fin (n + s)}
    (hw : D.cone O w) : gw (D.coneGates O) w := by
  intro h
  rw [mem_coneGates]
  convert hw using 1
  ext; simp; omega

theorem coneGates_closed (D : Dag n s) (O : Fin (n + s) → Prop) : D.GClosed (D.coneGates O) := by
  intro i hi a ha
  rw [gw_natAdd, mem_coneGates] at hi
  exact gw_coneGates (D.cone_closed O i hi a ha)

/-- A read-closed set of gates containing the gates of `O` contains the cone of `O`. -/
theorem coneGates_subset (D : Dag n s) (O : Fin (n + s) → Prop) {K : Finset (Fin s)}
    (hK : D.GClosed K) (hO : ∀ o, O o → gw K o) : D.coneGates O ⊆ K := by
  intro i hi
  rw [mem_coneGates] at hi
  exact gw_natAdd.mp (D.cone_subset hK hO _ hi)

/-- **Output deletion**: keep exactly the cone of the outputs `O`. -/
noncomputable def restrictOutputs (D : Dag n s) (O : Fin (n + s) → Prop) :
    Dag n (D.coneGates O).card :=
  D.keep (D.coneGates O)

/-- Every wire in the cone of `O` (in particular every output) keeps its value. -/
theorem val_restrictOutputs (D : Dag n s) (O : Fin (n + s) → Prop) (w : Fin (n + s))
    (hw : D.cone O w) :
    ∃ w' : Fin (n + (D.coneGates O).card), ∀ x, (D.restrictOutputs O).val x w' = D.val x w := by
  obtain ⟨w', hw'⟩ := exists_ew _ w (gw_coneGates hw)
  exact ⟨w', fun x => by rw [restrictOutputs, val_keep _ _ (D.coneGates_closed O), hw']⟩

/-- The gates outside every cone of `O`. -/
noncomputable def outsideGates (D : Dag n s) (O : Fin (n + s) → Prop) : Finset (Fin s) := by
  classical exact Finset.univ.filter fun i => ¬ D.cone O (Fin.natAdd n i)

/-- **Exact count**: `size(restrictOutputs O) + #(gates outside every cone of O) = s`. -/
theorem card_coneGates_add (D : Dag n s) (O : Fin (n + s) → Prop) :
    (D.coneGates O).card + (D.outsideGates O).card = s := by
  classical
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin s))) (fun i => D.cone O (Fin.natAdd n i))
  simpa [coneGates, outsideGates] using this

/-- **Subfamily (B8(3) shape).** A dag computing outputs `out i` (`i : Fin m`) yields, for every
subfamily `W`, a dag of size `s − #(gates outside the cones of W)` computing the same outputs. -/
theorem exists_subfamily {m : ℕ} (D : Dag n s) (out : Fin m → Fin (n + s)) (W : Finset (Fin m)) :
    ∃ (s' : ℕ) (D' : Dag n s'),
      s' + (D.outsideGates fun w => ∃ i ∈ W, out i = w).card = s ∧
      ∀ i ∈ W, ∃ o' : Fin (n + s'), ∀ x, D'.val x o' = D.val x (out i) := by
  refine ⟨_, D.restrictOutputs fun w => ∃ i ∈ W, out i = w, D.card_coneGates_add _, ?_⟩
  intro i hi
  exact D.val_restrictOutputs _ _ (D.subset_cone _ ⟨i, hi, rfl⟩)

/-! ## Restriction to a set of inputs: constants and copies on `A` -/

section Restrict

variable (D : Dag n s) (A : (Fin n → Bool) → Prop)

/-- Wire `w` is the constant `c` on `A`. -/
def ConstOn (w : Fin (n + s)) (c : Bool) : Prop := ∀ x, A x → D.val x w = c

/-- Wire `w` is constant on `A`. -/
def IsConst (w : Fin (n + s)) : Prop := ∃ c, D.ConstOn A w c

/-- Wires `u` and `w` agree on `A`. -/
def SameOn (u w : Fin (n + s)) : Prop := ∀ x, A x → D.val x u = D.val x w

/-- The representative of `w` on `A`: the FIRST wire equal to `w` on `A`. -/
noncomputable def rep (w : Fin (n + s)) : Fin (n + s) := by
  classical exact (Finset.min' (Finset.univ.filter fun u => D.SameOn A u w)
    ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩⟩)

variable {D A}

theorem rep_le_of_same {u w : Fin (n + s)} (h : D.SameOn A u w) : D.rep A w ≤ u := by
  classical
  unfold rep; exact Finset.min'_le _ u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem rep_le (w : Fin (n + s)) : D.rep A w ≤ w := rep_le_of_same fun _ _ => rfl

theorem rep_same (w : Fin (n + s)) : D.SameOn A (D.rep A w) w := by
  classical
  unfold rep
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun u => D.SameOn A u w) _)).2

theorem rep_eq_of_same {u w : Fin (n + s)} (h : D.SameOn A u w) : D.rep A u = D.rep A w :=
  le_antisymm (rep_le_of_same fun x hx => (rep_same w x hx).trans (h x hx).symm)
    (rep_le_of_same fun x hx => (rep_same u x hx).trans (h x hx))

theorem rep_rep (w : Fin (n + s)) : D.rep A (D.rep A w) = D.rep A w :=
  rep_eq_of_same (rep_same w)

theorem isConst_of_same {u w : Fin (n + s)} (h : D.SameOn A u w) (hu : D.IsConst A u) :
    D.IsConst A w :=
  let ⟨c, hc⟩ := hu; ⟨c, fun x hx => (h x hx).symm.trans (hc x hx)⟩

/-- A wire with a strictly earlier wire equal to it on `A` is not its own representative. -/
theorem rep_ne_of_same {u w : Fin (n + s)} (hu : u < w) (h : D.SameOn A u w) : D.rep A w ≠ w :=
  ne_of_lt (lt_of_le_of_lt (rep_le_of_same h) hu)

/-- A wire that survives the restriction: its own representative, and not constant on `A`. -/
def Canon (D : Dag n s) (A : (Fin n → Bool) → Prop) (w : Fin (n + s)) : Prop :=
  D.rep A w = w ∧ ¬ D.IsConst A w

theorem canon_rep {w : Fin (n + s)} (hw : ¬ D.IsConst A w) : D.Canon A (D.rep A w) :=
  ⟨rep_rep w, fun h => hw (isConst_of_same (rep_same w) h)⟩

variable (D A)

/-- What a read of wire `a` by gate `i` becomes: its constant, or its representative. -/
noncomputable def repSrc (i : Fin s) (a : Fin (n + i)) : Src (n + i) := by
  classical exact
    if h : D.IsConst A (lift i a) then Src.const h.choose
    else Src.wire ⟨(D.rep A (lift i a)).1,
      Nat.lt_of_le_of_lt (rep_le (lift i a)) (lift_lt i a)⟩

/-- **Propagation on `A`.** A gate constant on `A` becomes that constant; every other gate reads
representatives and constants instead of its wires, and is `prune`d. Same size. -/
noncomputable def prop : Dag n s := by
  classical exact ⟨fun i =>
    if h : D.IsConst A (Fin.natAdd n i) then KGate.const h.choose
    else ((D.gate i).bind (D.repSrc A i)).prune⟩

variable {D A}

theorem prop_gate_const {i : Fin s} (h : D.IsConst A (Fin.natAdd n i)) :
    ∃ c, (D.prop A).gate i = KGate.const c ∧ D.ConstOn A (Fin.natAdd n i) c := by
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold prop; simp only; rw [dif_pos h]

theorem prop_gate_nonconst {i : Fin s} (h : ¬ D.IsConst A (Fin.natAdd n i)) :
    (D.prop A).gate i = ((D.gate i).bind (D.repSrc A i)).prune := by
  unfold prop; simp only; rw [dif_neg h]

theorem repSrc_eval (i : Fin s) (a : Fin (n + i)) {x : Fin n → Bool} (hx : A x)
    {V : Fin (n + i) → Bool} (hV : ∀ b, V b = D.val x (lift i b)) :
    (D.repSrc A i a).eval V = D.val x (lift i a) := by
  unfold repSrc
  split_ifs with h
  · exact (h.choose_spec x hx).symm
  · rw [Src.eval_wire, hV]
    have e : lift i (⟨(D.rep A (lift i a)).1,
        Nat.lt_of_le_of_lt (rep_le (lift i a)) (lift_lt i a)⟩ : Fin (n + i)) =
        D.rep A (lift i a) := Fin.ext rfl
    rw [e]; exact rep_same _ x hx

/-- **Propagation is correct on `A`**: every wire keeps its value. -/
theorem val_prop {x : Fin n → Bool} (hx : A x) : ∀ w, (D.prop A).val x w = D.val x w := by
  refine wire_induction (fun j => by simp) (fun i ih => ?_)
  rw [val_natAdd]
  by_cases h : D.IsConst A (Fin.natAdd n i)
  · obtain ⟨c, hg, hc⟩ := prop_gate_const h
    rw [hg, KGate.eval_const, hc x hx]
  · rw [prop_gate_nonconst h, KGate.eval_prune, KGate.eval_bind, val_natAdd]
    congr 1
    funext a
    exact repSrc_eval i a hx ih

/-- After propagation every read is of a surviving wire. -/
theorem canon_of_mem_reads_prop {i : Fin s} {a : Fin (n + i)}
    (ha : a ∈ ((D.prop A).gate i).reads) : D.Canon A (lift i a) := by
  by_cases h : D.IsConst A (Fin.natAdd n i)
  · obtain ⟨c, hg, -⟩ := prop_gate_const h
    rw [hg, KGate.reads_const] at ha
    exact absurd ha (List.not_mem_nil)
  · rw [prop_gate_nonconst h] at ha
    obtain ⟨a', -, ha'⟩ := KGate.mem_reads_bind (KGate.mem_reads_prune ha)
    by_cases h' : D.IsConst A (lift i a')
    · unfold repSrc at ha'
      rw [dif_pos h'] at ha'
      exact absurd ha' (by simp)
    · unfold repSrc at ha'
      rw [dif_neg h'] at ha'
      have e : lift i a = D.rep A (lift i a') := by
        injection ha' with h1
        rw [← h1]; rfl
      rw [e]
      exact canon_rep h'

theorem prop_closed_canon : (D.prop A).Closed (D.Canon A) :=
  fun _ _ _ ha => canon_of_mem_reads_prop ha

/-- Shape: a propagated gate keeps its operation or is a constant (AND/OR, no input); its fan-in
does not grow. -/
theorem prop_gate_shape (i : Fin s) :
    (((D.prop A).gate i).op = (D.gate i).op ∨ (((D.prop A).gate i).inputs = [] ∧
      (((D.prop A).gate i).op = GateOp.and ∨ ((D.prop A).gate i).op = GateOp.or))) ∧
    ((D.prop A).gate i).inputs.length ≤ (D.gate i).inputs.length := by
  by_cases h : D.IsConst A (Fin.natAdd n i)
  · obtain ⟨c, hg, -⟩ := prop_gate_const h
    rw [hg]
    cases c <;> simp [KGate.const]
  · rw [prop_gate_nonconst h]
    refine ⟨?_, (KGate.prune_inputs_length _).trans (by simp)⟩
    rcases KGate.prune_op ((D.gate i).bind (D.repSrc A i)) with e | e
    · exact Or.inl (by rw [e]; rfl)
    · exact Or.inr e

/-- A propagated AND/OR/NOT gate has no constant-`true` input. -/
theorem prop_const_true (i : Fin s)
    (hop : (D.gate i).op = GateOp.and ∨ (D.gate i).op = GateOp.or ∨
      (D.gate i).op = GateOp.not) :
    Src.const true ∉ ((D.prop A).gate i).inputs := by
  by_cases h : D.IsConst A (Fin.natAdd n i)
  · obtain ⟨c, hg, -⟩ := prop_gate_const h
    rw [hg]; cases c <;> simp [KGate.const]
  · rw [prop_gate_nonconst h]
    exact KGate.const_true_not_mem_prune _ hop

variable (D A)

/-- The representatives of the outputs of `O` that are not constant on `A`. -/
def outReps (O : Fin (n + s) → Prop) (w : Fin (n + s)) : Prop :=
  ∃ o, O o ∧ ¬ D.IsConst A o ∧ D.rep A o = w

/-- The gates that survive the restriction to `A` with outputs `O`. -/
noncomputable def liveGates (O : Fin (n + s) → Prop) : Finset (Fin s) :=
  (D.prop A).coneGates (D.outReps A O)

/-- The gates that die: outside every cone of the (representatives of the) outputs after
propagation. -/
noncomputable def deadGates (O : Fin (n + s) → Prop) : Finset (Fin s) :=
  (D.prop A).outsideGates (D.outReps A O)

/-- **Restriction to `A`** (constant propagation, copy bypassing, dead-gate deletion). -/
noncomputable def simplify (O : Fin (n + s) → Prop) : Dag n (D.liveGates A O).card :=
  (D.prop A).restrictOutputs (D.outReps A O)

/-- **Exact size**: `size(simplify A O) + #dead = s`. -/
theorem card_simplify (O : Fin (n + s) → Prop) :
    (D.liveGates A O).card + (D.deadGates A O).card = s :=
  (D.prop A).card_coneGates_add _

variable {D A}

/-- **Correctness on `A`**: every output is constant on `A`, or is a wire of the restricted dag
with the same value on `A`. -/
theorem val_simplify (O : Fin (n + s) → Prop) (o : Fin (n + s)) (ho : O o) :
    D.IsConst A o ∨
      ∃ o' : Fin (n + (D.liveGates A O).card), ew _ o' = D.rep A o ∧
        ∀ x, A x → (D.simplify A O).val x o' = D.val x o := by
  by_cases h : D.IsConst A o
  · exact Or.inl h
  · right
    have hc := (D.prop A).subset_cone (D.outReps A O) (o := D.rep A o) ⟨o, ho, h, rfl⟩
    obtain ⟨o', ho'⟩ := exists_ew _ _ (gw_coneGates hc)
    refine ⟨o', ho', fun x hx => ?_⟩
    have := val_keep (D.prop A) _ ((D.prop A).coneGates_closed (D.outReps A O)) x o'
    rw [ho'] at this
    exact this.trans ((val_prop hx _).trans (rep_same o x hx))

/-- Every surviving gate is its own representative and not constant on `A`. -/
theorem canon_of_mem_liveGates {O : Fin (n + s) → Prop} {i : Fin s}
    (hi : i ∈ D.liveGates A O) : D.Canon A (Fin.natAdd n i) := by
  rw [liveGates, mem_coneGates] at hi
  refine (D.prop A).cone_subset prop_closed_canon ?_ _ hi
  rintro w ⟨o, -, hnc, rfl⟩
  exact canon_rep hnc

theorem mem_outsideGates {D : Dag n s} {O : Fin (n + s) → Prop} {i : Fin s} :
    i ∈ D.outsideGates O ↔ ¬ D.cone O (Fin.natAdd n i) := by
  classical simp [outsideGates]

theorem mem_deadGates {O : Fin (n + s) → Prop} {i : Fin s} :
    i ∈ D.deadGates A O ↔ i ∉ D.liveGates A O := by
  rw [deadGates, liveGates, mem_outsideGates, mem_coneGates]

/-- A gate that is constant on `A`, or equal on `A` to an earlier wire. -/
def ConstOrCopy (D : Dag n s) (A : (Fin n → Bool) → Prop) (i : Fin s) : Prop :=
  D.IsConst A (Fin.natAdd n i) ∨ D.rep A (Fin.natAdd n i) ≠ Fin.natAdd n i

/-- **Constant or copied gates die.** -/
theorem mem_deadGates_of_constOrCopy {O : Fin (n + s) → Prop} {i : Fin s}
    (h : D.ConstOrCopy A i) : i ∈ D.deadGates A O := by
  rw [mem_deadGates]
  intro hi
  obtain ⟨h1, h2⟩ := canon_of_mem_liveGates hi
  rcases h with h | h
  · exact h2 h
  · exact h h1

theorem constOrCopy_of_const {i : Fin s} {c : Bool} (h : D.ConstOn A (Fin.natAdd n i) c) :
    D.ConstOrCopy A i := Or.inl ⟨c, h⟩

theorem constOrCopy_of_copy {i : Fin s} {u : Fin (n + s)} (hu : u < Fin.natAdd n i)
    (h : D.SameOn A u (Fin.natAdd n i)) : D.ConstOrCopy A i := Or.inr (rep_ne_of_same hu h)

/-- A gate all of whose reads are constant on `A` is constant on `A`. -/
theorem isConst_of_reads {i : Fin s} (h : ∀ a ∈ (D.gate i).reads, D.IsConst A (lift i a)) :
    D.IsConst A (Fin.natAdd n i) := by
  by_cases hA : ∃ x0, A x0
  · obtain ⟨x0, hx0⟩ := hA
    refine ⟨D.val x0 (Fin.natAdd n i), fun x hx => ?_⟩
    rw [val_natAdd, val_natAdd]
    refine KGate.eval_congr fun a ha => ?_
    obtain ⟨c, hc⟩ := h a ha
    rw [hc x hx, hc x0 hx0]
  · exact ⟨false, fun x hx => absurd ⟨x, hx⟩ hA⟩

/-- Gate `i` reads wire `w` EFFECTIVELY: an AND/OR gate of fan-in ≤ 2 reading `w`, or a NOT
gate whose first input is `w`. -/
def EffReads (D : Dag n s) (i : Fin s) (w : Fin (n + s)) : Prop :=
  (((D.gate i).op = GateOp.and ∨ (D.gate i).op = GateOp.or) ∧ (D.gate i).inputs.length ≤ 2 ∧
    ∃ a ∈ (D.gate i).reads, lift i a = w) ∨
  ((D.gate i).op = GateOp.not ∧ ∃ a, (D.gate i).inputs.head? = some (Src.wire a) ∧ lift i a = w)

/-- **An effective reader of a constant wire is constant or a copy.** -/
theorem constOrCopy_of_effReads {i : Fin s} {w : Fin (n + s)} (h : D.EffReads i w)
    (hw : D.IsConst A w) : D.ConstOrCopy A i := by
  -- `Gd f`: on `A`, `f` is constant or a wire below gate `i`.
  let Gd : ((Fin n → Bool) → Bool) → Prop := fun f =>
    (∃ c, ∀ x, A x → f x = c) ∨ ∃ u : Fin (n + i), ∀ x, A x → f x = D.val x (lift i u)
  have gd_gate : Gd (fun x => D.val x (Fin.natAdd n i)) → D.ConstOrCopy A i := by
    rintro (⟨c, hc⟩ | ⟨u, hu⟩)
    · exact Or.inl ⟨c, hc⟩
    · exact constOrCopy_of_copy (u := lift i u) (by rw [Fin.lt_def]; simp)
        fun x hx => (hu x hx).symm
  have gd_congr : ∀ f g, (∀ x, A x → f x = g x) → Gd g → Gd f := by
    rintro f g hfg (⟨c, hc⟩ | ⟨u, hu⟩)
    · exact Or.inl ⟨c, fun x hx => (hfg x hx).trans (hc x hx)⟩
    · exact Or.inr ⟨u, fun x hx => (hfg x hx).trans (hu x hx)⟩
  let V : (Fin n → Bool) → Fin (n + i) → Bool := fun x a => D.val x (lift i a)
  have gd_src : ∀ t : Src (n + i), Gd (fun x => t.eval (V x)) := by
    intro t
    cases t with
    | wire u => exact Or.inr ⟨u, fun _ _ => rfl⟩
    | const b => exact Or.inl ⟨b, fun _ _ => rfl⟩
  have comb : ∀ (f g : (Fin n → Bool) → Bool) (c : Bool), (∀ x, A x → f x = c) → Gd g →
      Gd (fun x => f x && g x) ∧ Gd (fun x => g x && f x) ∧ Gd (fun x => f x || g x) ∧
        Gd (fun x => g x || f x) := by
    intro f g c hf hg
    cases c
    · refine ⟨Or.inl ⟨false, fun x hx => by simp [hf x hx]⟩,
        Or.inl ⟨false, fun x hx => by simp [hf x hx]⟩,
        gd_congr _ g (fun x hx => by simp [hf x hx]) hg,
        gd_congr _ g (fun x hx => by simp [hf x hx]) hg⟩
    · refine ⟨gd_congr _ g (fun x hx => by simp [hf x hx]) hg,
        gd_congr _ g (fun x hx => by simp [hf x hx]) hg,
        Or.inl ⟨true, fun x hx => by simp [hf x hx]⟩,
        Or.inl ⟨true, fun x hx => by simp [hf x hx]⟩⟩
  apply gd_gate
  have hv : ∀ x, D.val x (Fin.natAdd n i) = (D.gate i).eval (V x) := fun x => val_natAdd D x i
  apply gd_congr _ (fun x => (D.gate i).eval (V x)) (fun x _ => hv x)
  obtain ⟨c, hc⟩ := hw
  unfold EffReads at h
  generalize D.gate i = g at h ⊢
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨hop, hlen, a, ha, rfl⟩ | ⟨hop, a, hhd, rfl⟩
  · simp only at hop hlen
    rw [KGate.mem_reads] at ha
    have hca : ∀ x, A x → (Src.wire a).eval (V x) = c := fun x hx => hc x hx
    rcases ins with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, rest⟩⟩⟩
    · simp at ha
    · simp only [List.mem_singleton] at ha
      subst ha
      refine Or.inl ⟨c, fun x hx => ?_⟩
      rcases hop with rfl | rfl <;> simp [KGate.eval, GateOp.eval, ← hca x hx]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases hop with rfl | rfl
      · refine gd_congr _ (fun x => t1.eval (V x) && t2.eval (V x))
          (fun x _ => by simp [KGate.eval, GateOp.eval]) ?_
        rcases ha with rfl | rfl
        · exact (comb _ _ c hca (gd_src t2)).1
        · exact (comb _ _ c hca (gd_src t1)).2.1
      · refine gd_congr _ (fun x => t1.eval (V x) || t2.eval (V x))
          (fun x _ => by simp [KGate.eval, GateOp.eval]) ?_
        rcases ha with rfl | rfl
        · exact (comb _ _ c hca (gd_src t2)).2.2.1
        · exact (comb _ _ c hca (gd_src t1)).2.2.2
    · simp at hlen
  · change op = GateOp.not at hop
    change ins.head? = _ at hhd
    subst hop
    rcases ins with _ | ⟨t1, rest⟩
    · simp at hhd
    · simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      exact Or.inl ⟨!c, fun x hx => by
        simp [KGate.eval, GateOp.eval, show V x a = c from hc x hx]⟩

open Classical in
/-- **Readers of a constant wire die**: the effective readers of a wire constant on `A` are at
most the dead gates. -/
theorem card_effReaders_le (O : Fin (n + s) → Prop) {w : Fin (n + s)} (hw : D.IsConst A w) :
    (Finset.univ.filter fun i => D.EffReads i w).card ≤ (D.deadGates A O).card := by
  classical
  refine Finset.card_le_card fun i hi => ?_
  exact mem_deadGates_of_constOrCopy (constOrCopy_of_effReads (Finset.mem_filter.mp hi).2 hw)

end Restrict

/-! ### Fixing one variable -/

/-- **Variable restriction** `x_v := b` with outputs `O`. -/
noncomputable def restrictVar (D : Dag n s) (v : Fin n) (b : Bool) (O : Fin (n + s) → Prop) :=
  D.simplify (fun x => x v = b) O

theorem isConst_var (D : Dag n s) (v : Fin n) (b : Bool) :
    D.IsConst (fun x => x v = b) (Fin.castAdd s v) := ⟨b, fun x hx => by simp [hx]⟩

open Classical in
/-- **N2/N3 shape**: `#(effective readers of x_v) ≤ #dead(x_v := b) = s − size`. -/
theorem card_readers_le (D : Dag n s) (v : Fin n) (b : Bool) (O : Fin (n + s) → Prop) :
    (Finset.univ.filter fun i => D.EffReads i (Fin.castAdd s v)).card ≤
      (D.deadGates (fun x => x v = b) O).card :=
  card_effReaders_le O (D.isConst_var v b)

/-- **Variable restriction, on all inputs.** Every output is constant on `{x v = b}`, or is a
wire of `restrictVar v b O` which, on EVERY input `x`, carries the value of the original output at
`x` with `x_v := b` (the restricted dag does not read `x_v`). -/
theorem val_restrictVar (D : Dag n s) (v : Fin n) (b : Bool) (O : Fin (n + s) → Prop)
    (o : Fin (n + s)) (ho : O o) :
    D.IsConst (fun x => x v = b) o ∨
      ∃ o' : Fin (n + (D.liveGates (fun x => x v = b) O).card),
        ∀ x, (D.restrictVar v b O).val x o' = D.val (Function.update x v b) o := by
  by_cases h : D.IsConst (fun x => x v = b) o
  · exact Or.inl h
  right
  rcases val_simplify (A := fun x => x v = b) O o ho with h' | ⟨o', ho', hv⟩
  · exact absurd h' h
  refine ⟨o', fun x => ?_⟩
  rw [← hv _ (by simp)]
  refine agree_off _ x _ (fun w => ew _ w = Fin.castAdd s v) (fun j hj => ?_)
    (fun t _ a ha hbad => ?_) o' ?_
  · rw [ew_castAdd] at hj
    have hjv : j ≠ v := fun e => hj (by rw [e])
    exact (Function.update_of_ne hjv _ _).symm
  · obtain ⟨a', ha', he⟩ := mem_reads_keep ha
    have hb2 := he.symm.trans hbad
    exact (canon_of_mem_reads_prop ha').2 (by rw [hb2]; exact D.isConst_var v b)
  · intro hbad
    rw [ho'] at hbad
    exact (canon_rep h).2 (by rw [hbad]; exact D.isConst_var v b)

end Dag

end PEqualNP.Kernel
