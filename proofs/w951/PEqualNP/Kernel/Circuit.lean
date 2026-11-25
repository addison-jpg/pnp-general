import Mathlib
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Kernel/Circuit: a well-scoped DAG over the `GateOp` basis, any fan-in

`Dag n s` is a circuit on `n` inputs with `s` gates. Wires are `Fin (n + s)`: wire `j < n` is
input `j` (`Fin.castAdd s j`), wire `n + i` is gate `i` (`Fin.natAdd n i`). Gate `i` is a
`KGate (n + i)`, so it can only name wires below itself: there is no "missing wire reads false"
case, no `getD`, and no well-formedness hypothesis to carry.

A gate has the shape of the project's list gates (`PEqualNP.CircuitLowerBounds.Gate`): an
operation `op : GateOp` (AND / OR / NOT / MOD m / MAJ, semantics `GateOp.eval` on the list of
input values) and a list `inputs` of any length. An input is a `Src k`: a wire `Fin k` or a
constant. Constants make every pass arity-preserving (`subst` replaces a fixed wire by its
constant, in place) and make the translation from list circuits total (a dangling read is the
constant `false`).

Contents.

* `Src k`, `KGate k` (`op`, `inputs`), `KGate.eval`, `KGate.reads`, `OpMono`.
* `Dag.val` with the two unfolding lemmas `val_castAdd` and `val_natAdd` (both `simp`).
* `Dag.wire_induction`: THE proof principle (inputs, then a gate from the wires it can name).
* `Dag.val_rel`: one relational transfer lemma between two dags; `agree_off`, `val_mono`,
  the sandwich and `val_mask` are instances.
* prefix / snoc: `take`, `snoc`, `init`, `last`, `snocInduction`.
* passes, each with its value lemma: `restrict` (fix inputs to constants; `restrictGE z` is the
  subcube `{x ≥ z}`), `mask` (gates outside a set become `const false`) with `Closed` and
  `cone`, `constNot b` (every NOT becomes the constant `b`) with `sandwich`.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds (GateOp)

/-! ## Monotone operations -/

/-- The operation is monotone in the list of its input values (same length, pointwise `≤`). -/
def OpMono (op : GateOp) : Prop :=
  ∀ l l' : List Bool, List.Forall₂ (· ≤ ·) l l' → op.eval l ≤ op.eval l'

theorem opMono_and : OpMono GateOp.and := by
  intro l l' h
  induction h with
  | nil => exact le_rfl
  | @cons a b l l' hab _ ih =>
    simp only [GateOp.eval, List.all_cons, id] at ih ⊢
    revert hab ih
    cases a <;> cases b <;> cases l.all id <;> cases l'.all id <;> decide

theorem opMono_or : OpMono GateOp.or := by
  intro l l' h
  induction h with
  | nil => exact le_rfl
  | @cons a b l l' hab _ ih =>
    simp only [GateOp.eval, List.any_cons, id] at ih ⊢
    revert hab ih
    cases a <;> cases b <;> cases l.any id <;> cases l'.any id <;> decide

theorem opMono_maj : OpMono GateOp.maj := by
  intro l l' h
  have hlen := h.length_eq
  have hc : l.count true ≤ l'.count true := by
    induction h with
    | nil => exact le_rfl
    | @cons a b l l' hab h ih =>
      have := ih h.length_eq
      revert hab
      cases a <;> cases b <;> simp <;> omega
  rw [Bool.le_iff_imp]
  simp only [GateOp.eval, decide_eq_true_eq]
  omega

/-- AND and OR, the monotone operations W951 uses. -/
theorem opMono_of_and_or {op : GateOp} (h : op = GateOp.and ∨ op = GateOp.or) : OpMono op := by
  rcases h with rfl | rfl
  · exact opMono_and
  · exact opMono_or

/-! ## Gate inputs -/

/-- What a gate input may be: a wire below the gate, or a constant. -/
inductive Src (k : ℕ) where
  | wire (a : Fin k)
  | const (b : Bool)
  deriving DecidableEq, Repr

namespace Src

variable {k k' : ℕ}

/-- The value of an input, given the wire values. -/
def eval (v : Fin k → Bool) : Src k → Bool
  | wire a => v a
  | const b => b

@[simp] theorem eval_wire (v : Fin k → Bool) (a : Fin k) : (wire a).eval v = v a := rfl
@[simp] theorem eval_const (v : Fin k → Bool) (b : Bool) : (const b : Src k).eval v = b := rfl

/-- The wire an input reads, if any. -/
def wire? : Src k → Option (Fin k)
  | wire a => some a
  | const _ => none

@[simp] theorem wire?_wire (a : Fin k) : (wire a).wire? = some a := rfl
@[simp] theorem wire?_const (b : Bool) : (const b : Src k).wire? = none := rfl

theorem wire?_eq_some {s : Src k} {a : Fin k} : s.wire? = some a ↔ s = wire a := by
  cases s <;> simp

/-- Rename the wire. -/
def map (f : Fin k → Fin k') : Src k → Src k'
  | wire a => wire (f a)
  | const b => const b

@[simp] theorem eval_map (f : Fin k → Fin k') (s : Src k) (v : Fin k' → Bool) :
    (s.map f).eval v = s.eval (v ∘ f) := by cases s <;> rfl

/-- Replace a fixed wire (`ρ a = some c`) by its constant. -/
def subst (ρ : Fin k → Option Bool) : Src k → Src k
  | wire a => (ρ a).elim (wire a) const
  | const b => const b

end Src

/-! ## Gates -/

/-- A gate that may read the wires `Fin k`: an operation and its inputs, in order, any number,
repetitions allowed. -/
structure KGate (k : ℕ) where
  /-- The operation. -/
  op : GateOp
  /-- The inputs. -/
  inputs : List (Src k)

namespace KGate

variable {k k' : ℕ}

/-- The value of a gate, given the values of the wires it may read. -/
def eval (v : Fin k → Bool) (g : KGate k) : Bool := g.op.eval (g.inputs.map (Src.eval v))

theorem eval_def (v : Fin k → Bool) (g : KGate k) :
    g.eval v = g.op.eval (g.inputs.map (Src.eval v)) := rfl

/-- The wires a gate reads. -/
def reads (g : KGate k) : List (Fin k) := g.inputs.filterMap Src.wire?

theorem mem_reads {g : KGate k} {a : Fin k} : a ∈ g.reads ↔ Src.wire a ∈ g.inputs := by
  simp [reads, List.mem_filterMap, Src.wire?_eq_some]

/-- The constant gate: `OR []` is `false`, `AND []` is `true`. -/
def const (b : Bool) : KGate k := ⟨bif b then GateOp.and else GateOp.or, []⟩

@[simp] theorem eval_const (v : Fin k → Bool) (b : Bool) : (const b : KGate k).eval v = b := by
  cases b <;> rfl

@[simp] theorem reads_const (b : Bool) : (const b : KGate k).reads = [] := rfl

theorem opMono_const (b : Bool) : OpMono (const b : KGate k).op := by
  cases b
  · exact opMono_or
  · exact opMono_and

/-- Is this a NOT gate? -/
def isNot (g : KGate k) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

theorem isNot_iff {g : KGate k} : g.isNot = true ↔ g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]

@[simp] theorem isNot_const (b : Bool) : (const b : KGate k).isNot = false := by
  cases b <;> rfl

/-- A NOT gate negates its first input (`true` on no inputs). -/
theorem eval_of_isNot {g : KGate k} (hg : g.isNot = true) (v : Fin k → Bool) :
    g.eval v = !((g.inputs.map (Src.eval v)).headD false) := by
  rw [eval_def, isNot_iff.mp hg]; rfl

/-- A gate's value depends only on the wires it reads. This is the gate-level core of every
"the two circuits agree here" argument. -/
theorem eval_congr {g : KGate k} {v v' : Fin k → Bool} (h : ∀ a ∈ g.reads, v a = v' a) :
    g.eval v = g.eval v' := by
  unfold eval
  congr 1
  refine List.map_congr_left fun s hs => ?_
  cases s with
  | wire a => exact h a (mem_reads.mpr hs)
  | const b => rfl

/-- Gates with a monotone operation (AND, OR, MAJ, constants) are monotone. -/
theorem eval_mono {g : KGate k} (hg : OpMono g.op) {v v' : Fin k → Bool}
    (h : ∀ a ∈ g.reads, v a ≤ v' a) : g.eval v ≤ g.eval v' := by
  refine hg _ _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro s hs
  cases s with
  | wire a => exact h a (mem_reads.mpr hs)
  | const b => exact le_rfl

/-- Rename the wires of a gate. -/
def map (f : Fin k → Fin k') (g : KGate k) : KGate k' := ⟨g.op, g.inputs.map (Src.map f)⟩

@[simp] theorem eval_map (f : Fin k → Fin k') (g : KGate k) (v : Fin k' → Bool) :
    (g.map f).eval v = g.eval (v ∘ f) := by
  simp only [eval, map, List.map_map]
  congr 1
  exact List.map_congr_left fun s _ => Src.eval_map f s v

@[simp] theorem reads_map (f : Fin k → Fin k') (g : KGate k) :
    (g.map f).reads = g.reads.map f := by
  obtain ⟨op, ins⟩ := g
  show (ins.map (Src.map f)).filterMap Src.wire? = (ins.filterMap Src.wire?).map f
  induction ins with
  | nil => rfl
  | cons s l ih =>
    cases s <;> simp only [List.map_cons, List.filterMap_cons, Src.map, Src.wire?, ih]

@[simp] theorem isNot_map (f : Fin k → Fin k') (g : KGate k) : (g.map f).isNot = g.isNot := rfl

/-- Replace a NOT gate by the constant `b`. -/
def constNot (b : Bool) (g : KGate k) : KGate k := bif g.isNot then const b else g

@[simp] theorem isNot_constNot (b : Bool) (g : KGate k) : (g.constNot b).isNot = false := by
  unfold constNot
  cases h : g.isNot <;> simp [h]

theorem constNot_of_isNot_false (b : Bool) {g : KGate k} (hg : g.isNot = false) :
    g.constNot b = g := by
  simp [constNot, hg]

theorem constNot_of_isNot (b : Bool) {g : KGate k} (hg : g.isNot = true) :
    g.constNot b = const b := by
  simp [constNot, hg]

/-- If the non-NOT gate is monotone, so is the result. -/
theorem opMono_constNot (b : Bool) {g : KGate k} (hg : g.isNot = false → OpMono g.op) :
    OpMono (g.constNot b).op := by
  cases h : g.isNot
  · rw [constNot_of_isNot_false b h]; exact hg h
  · rw [constNot_of_isNot b h]; exact opMono_const b

/-- Substitute constants for some of the wires (`ρ a = some c` fixes wire `a` to `c`): each
fixed input becomes the constant, in place. The operation, the number of inputs and the gate
count are kept, and the result reads no fixed wire. -/
def subst (ρ : Fin k → Option Bool) (g : KGate k) : KGate k := ⟨g.op, g.inputs.map (Src.subst ρ)⟩

@[simp] theorem subst_op (ρ : Fin k → Option Bool) (g : KGate k) : (g.subst ρ).op = g.op := rfl

/-- Substitution is sound wherever the wire values respect the fixed constants. -/
theorem eval_subst (ρ : Fin k → Option Bool) (g : KGate k) (v : Fin k → Bool)
    (h : ∀ a ∈ g.reads, ∀ c, ρ a = some c → v a = c) : (g.subst ρ).eval v = g.eval v := by
  simp only [eval, subst, List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  cases s with
  | const b => rfl
  | wire a =>
    have ha := h a (mem_reads.mpr hs)
    rcases hρ : ρ a with _ | c
    · simp [Src.subst, hρ]
    · simp [Src.subst, hρ, ha c hρ]

/-- After substitution a gate reads only unfixed wires (and only wires it read before). -/
theorem mem_reads_subst {ρ : Fin k → Option Bool} {g : KGate k} {a : Fin k}
    (h : a ∈ (g.subst ρ).reads) : ρ a = none ∧ a ∈ g.reads := by
  rw [mem_reads] at h ⊢
  obtain ⟨s, hs, hsa⟩ := List.mem_map.mp h
  cases s with
  | const b => simp [Src.subst] at hsa
  | wire a' =>
    rcases hρ : ρ a' with _ | c
    · simp only [Src.subst, hρ, Option.elim, Src.wire.injEq] at hsa
      subst hsa
      exact ⟨hρ, hs⟩
    · simp [Src.subst, hρ] at hsa

theorem isNot_subst (ρ : Fin k → Option Bool) {g : KGate k} (hg : g.isNot = false) :
    (g.subst ρ).isNot = false := hg

end KGate

/-! ## The DAG -/

/-- A circuit on `n` inputs with `s` gates; gate `i` reads wires below `n + i`. -/
@[ext] structure Dag (n s : ℕ) where
  /-- The gates, in order. -/
  gate : (i : Fin s) → KGate (n + i)

/-- A wire that gate `i` can name, as a wire of the whole circuit. -/
def lift {n s : ℕ} (i : Fin s) (a : Fin (n + i)) : Fin (n + s) := ⟨a.1, by omega⟩

@[simp] theorem lift_val {n s : ℕ} (i : Fin s) (a : Fin (n + i)) : (lift i a).1 = a.1 := rfl

theorem lift_lt {n s : ℕ} (i : Fin s) (a : Fin (n + i)) : (lift i a).1 < n + i := a.2

theorem lift_injective {n s : ℕ} (i : Fin s) : Function.Injective (lift (n := n) i) :=
  fun a b h => Fin.ext (by simpa [lift] using congrArg Fin.val h)

namespace Dag

variable {n s : ℕ}

/-- Values of the first `n + k` wires, by recursion on the number `k` of gates evaluated. -/
def vals (D : Dag n s) (x : Fin n → Bool) : (k : ℕ) → k ≤ s → Fin (n + k) → Bool
  | 0, _ => fun w => x w
  | k + 1, h => fun w =>
    if hw : w.1 < n + k then vals D x k (by omega) ⟨w.1, hw⟩
    else (D.gate ⟨k, h⟩).eval (vals D x k (by omega))

theorem vals_eq (D : Dag n s) (x : Fin n → Bool) (k : ℕ) :
    ∀ (k' : ℕ) (_ : k ≤ k') (hk' : k' ≤ s) (w : Fin (n + k')) (hw : w.1 < n + k),
      D.vals x k' hk' w = D.vals x k (by omega) ⟨w.1, hw⟩ := by
  intro k' hkk'
  induction k', hkk' using Nat.le_induction with
  | base => intro _ w hw; rfl
  | succ k' hkk' ih =>
    intro hk' w hw
    have hw' : w.1 < n + k' := by omega
    rw [vals]
    simp only [hw', ↓reduceDIte]
    exact ih (by omega) ⟨w.1, hw'⟩ hw

/-- The value of wire `w` on input `x`. -/
def val (D : Dag n s) (x : Fin n → Bool) (w : Fin (n + s)) : Bool := D.vals x s le_rfl w

/-- An input wire carries the input. -/
@[simp] theorem val_castAdd (D : Dag n s) (x : Fin n → Bool) (j : Fin n) :
    D.val x (Fin.castAdd s j) = x j := by
  unfold val
  rw [vals_eq D x 0 s (Nat.zero_le _) le_rfl _ (by simp)]
  rfl

/-- A gate wire carries the gate applied to the wires it names. -/
@[simp] theorem val_natAdd (D : Dag n s) (x : Fin n → Bool) (i : Fin s) :
    D.val x (Fin.natAdd n i) = (D.gate i).eval fun a => D.val x (lift i a) := by
  unfold val
  rw [vals_eq D x (i + 1) s i.2 le_rfl _ (by simp)]
  rw [vals]
  simp only [Fin.val_natAdd, lt_self_iff_false, ↓reduceDIte]
  congr 1
  funext a
  exact (vals_eq D x i s i.2.le le_rfl (lift i a) a.2).symm

/-- `val_natAdd` under the name the W951 files use. -/
theorem val_gate (D : Dag n s) (x : Fin n → Bool) (i : Fin s) :
    D.val x (Fin.natAdd n i) = (D.gate i).eval fun a => D.val x (lift i a) :=
  D.val_natAdd x i

/-- Every wire is an input wire or a gate wire. -/
theorem wire_cases {P : Fin (n + s) → Prop} (hin : ∀ j : Fin n, P (Fin.castAdd s j))
    (hg : ∀ i : Fin s, P (Fin.natAdd n i)) : ∀ w, P w := by
  intro w
  by_cases h : w.1 < n
  · exact (show w = Fin.castAdd s ⟨w.1, h⟩ from Fin.ext rfl) ▸ hin ⟨w.1, h⟩
  · exact (show w = Fin.natAdd n ⟨w.1 - n, by omega⟩ from Fin.ext (by simp; omega)) ▸
      hg ⟨w.1 - n, by omega⟩

/-- **Wire induction.** To prove `P` for every wire: prove it for the inputs, and for gate `i`
from all the wires gate `i` can name. -/
theorem wire_induction {P : Fin (n + s) → Prop} (hin : ∀ j : Fin n, P (Fin.castAdd s j))
    (hg : ∀ i : Fin s, (∀ a : Fin (n + i), P (lift i a)) → P (Fin.natAdd n i)) : ∀ w, P w := by
  have key : ∀ m : ℕ, ∀ w : Fin (n + s), w.1 < m → P w := by
    intro m
    induction m with
    | zero => intro w hw; omega
    | succ m ih =>
      intro w hw
      revert hw
      refine wire_cases (P := fun w => w.1 < m + 1 → P w) (fun j _ => hin j) (fun i hi => ?_) w
      exact hg i fun a => ih _ (by have := a.2; simp at hi ⊢; omega)
  exact fun w => key (w.1 + 1) w (Nat.lt_succ_self _)

/-- The value at a natural-number wire index, `false` past the end (the W951 convention). -/
def valN (D : Dag n s) (x : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n + s then D.val x ⟨i, h⟩ else false

theorem valN_of_lt (D : Dag n s) (x : Fin n → Bool) {i : ℕ} (h : i < n + s) :
    D.valN x i = D.val x ⟨i, h⟩ := by simp [valN, h]

theorem valN_of_ge (D : Dag n s) (x : Fin n → Bool) {i : ℕ} (h : n + s ≤ i) :
    D.valN x i = false := by simp [valN, show ¬ i < n + s by omega]

@[simp] theorem valN_val (D : Dag n s) (x : Fin n → Bool) (w : Fin (n + s)) :
    D.valN x w.1 = D.val x w := by simp [valN]

/-! ## One transfer lemma -/

/-- **Relational transfer.** Two dags of the same shape, two inputs, a relation `R` on values
and a set `G` of wires. If the inputs in `G` are related, and every gate in `G` maps wire
values related on `G` to related values, then all wires in `G` are related.

`agree_off` (R = equality, same dag), `val_mono` (R = `≤`, same dag), the sandwich (R = `≤`,
same input) and `val_mask` (R = equality, same input) are all this lemma. -/
theorem val_rel (D D' : Dag n s) (x y : Fin n → Bool) (R : Bool → Bool → Prop)
    (G : Fin (n + s) → Prop)
    (hin : ∀ j : Fin n, G (Fin.castAdd s j) → R (x j) (y j))
    (hg : ∀ i : Fin s, G (Fin.natAdd n i) → ∀ v v' : Fin (n + i) → Bool,
      (∀ a, G (lift i a) → R (v a) (v' a)) → R ((D.gate i).eval v) ((D'.gate i).eval v')) :
    ∀ w, G w → R (D.val x w) (D'.val y w) := by
  refine wire_induction (fun j hj => ?_) (fun i ih hi => ?_)
  · simpa using hin j hj
  · simp only [val_natAdd]
    exact hg i hi _ _ ih

/-- **Agreement off a bad set.** If the two inputs agree outside `Bad` and every gate outside
`Bad` reads only wires outside `Bad`, then every wire outside `Bad` has the same value. -/
theorem agree_off (D : Dag n s) (x y : Fin n → Bool) (Bad : Fin (n + s) → Prop)
    (hin : ∀ j : Fin n, ¬ Bad (Fin.castAdd s j) → x j = y j)
    (hg : ∀ i : Fin s, ¬ Bad (Fin.natAdd n i) → ∀ a ∈ (D.gate i).reads, ¬ Bad (lift i a)) :
    ∀ w, ¬ Bad w → D.val x w = D.val y w :=
  val_rel D D x y Eq (fun w => ¬ Bad w) hin fun i hi _ _ hv =>
    KGate.eval_congr fun a ha => hv a (hg i hi a ha)

/-- Two-dag form of `agree_off`: additionally the two dags have the same gates outside `Bad`. -/
theorem agree_off₂ (D D' : Dag n s) (x y : Fin n → Bool) (Bad : Fin (n + s) → Prop)
    (hin : ∀ j : Fin n, ¬ Bad (Fin.castAdd s j) → x j = y j)
    (hg : ∀ i : Fin s, ¬ Bad (Fin.natAdd n i) →
      D.gate i = D'.gate i ∧ ∀ a ∈ (D.gate i).reads, ¬ Bad (lift i a)) :
    ∀ w, ¬ Bad w → D.val x w = D'.val y w :=
  val_rel D D' x y Eq (fun w => ¬ Bad w) hin fun i hi _ _ hv => by
    rw [← (hg i hi).1]
    exact KGate.eval_congr fun a ha => hv a ((hg i hi).2 a ha)

/-- A dag with no NOT gate. -/
def NotFree (D : Dag n s) : Prop := ∀ i, (D.gate i).isNot = false

/-- A dag all of whose gates have a monotone operation (AND, OR, MAJ; any fan-in). -/
def Mono (D : Dag n s) : Prop := ∀ i, OpMono (D.gate i).op

/-- A dag whose gates are NOT gates or monotone gates (the hypothesis of the sandwich). -/
def MonoOffNot (D : Dag n s) : Prop := ∀ i, (D.gate i).isNot = false → OpMono (D.gate i).op

theorem Mono.monoOffNot {D : Dag n s} (hD : D.Mono) : D.MonoOffNot := fun i _ => hD i

/-- AND/OR dags are monotone dags. -/
theorem mono_of_and_or (D : Dag n s)
    (h : ∀ i, (D.gate i).op = GateOp.and ∨ (D.gate i).op = GateOp.or) : D.Mono :=
  fun i => opMono_of_and_or (h i)

/-- **Monotonicity** of dags with monotone gates. -/
theorem val_mono (D : Dag n s) (hD : D.Mono) {x y : Fin n → Bool} (hxy : x ≤ y)
    (w : Fin (n + s)) : D.val x w ≤ D.val y w :=
  val_rel D D x y (· ≤ ·) (fun _ => True) (fun j _ => hxy j)
    (fun i _ _ _ hv => KGate.eval_mono (hD i) fun a _ => hv a trivial) w trivial

/-- Gatewise domination gives wirewise domination (used for the sandwich). -/
theorem val_le_val (D D' : Dag n s) {x y : Fin n → Bool} (hxy : x ≤ y)
    (hg : ∀ (i : Fin s) (v v' : Fin (n + i) → Bool), v ≤ v' → (D.gate i).eval v ≤ (D'.gate i).eval v')
    (w : Fin (n + s)) : D.val x w ≤ D'.val y w :=
  val_rel D D' x y (· ≤ ·) (fun _ => True) (fun j _ => hxy j)
    (fun i _ v v' hv => hg i v v' fun a => hv a trivial) w trivial

/-! ## Prefix and snoc -/

/-- The first `k` gates. -/
def take (D : Dag n s) (k : ℕ) (hk : k ≤ s) : Dag n k := ⟨fun i => D.gate ⟨i.1, by omega⟩⟩

@[simp] theorem take_gate (D : Dag n s) (k : ℕ) (hk : k ≤ s) (i : Fin k) :
    (D.take k hk).gate i = D.gate ⟨i.1, by omega⟩ := rfl

/-- A prefix computes the same values on its wires. -/
theorem val_take (D : Dag n s) (k : ℕ) (hk : k ≤ s) (x : Fin n → Bool) (w : Fin (n + k)) :
    (D.take k hk).val x w = D.val x ⟨w.1, by omega⟩ := by
  revert w
  refine wire_induction (fun j => ?_) (fun i ih => ?_)
  · exact ((D.take k hk).val_castAdd x j).trans (D.val_castAdd x j).symm
  · have e := D.val_natAdd x ⟨i.1, by omega⟩
    rw [val_natAdd, take_gate]
    refine Eq.trans ?_ e.symm
    exact KGate.eval_congr fun a _ => ih a

/-- The empty dag. -/
def nil : Dag n 0 := ⟨fun i => i.elim0⟩

@[simp] theorem val_nil (x : Fin n → Bool) (w : Fin (n + 0)) : (nil : Dag n 0).val x w = x w :=
  rfl

/-- Append one gate. -/
def snoc (D : Dag n s) (g : KGate (n + s)) : Dag n (s + 1) :=
  ⟨fun i => if h : i.1 < s then D.gate ⟨i.1, h⟩
    else (show n + s = n + i.1 by have := i.2; omega) ▸ g⟩

/-- All gates but the last. -/
def init (D : Dag n (s + 1)) : Dag n s := D.take s (Nat.le_succ s)

/-- The last gate. -/
def last (D : Dag n (s + 1)) : KGate (n + s) := D.gate (Fin.last s)

@[simp] theorem snoc_gate_castSucc (D : Dag n s) (g : KGate (n + s)) (i : Fin s) :
    (D.snoc g).gate i.castSucc = D.gate i := by
  simp [snoc]

@[simp] theorem snoc_gate_last (D : Dag n s) (g : KGate (n + s)) :
    (D.snoc g).gate (Fin.last s) = g := by
  simp [snoc]

@[simp] theorem init_snoc (D : Dag n s) (g : KGate (n + s)) : (D.snoc g).init = D := by
  ext i
  exact snoc_gate_castSucc D g i

@[simp] theorem last_snoc (D : Dag n s) (g : KGate (n + s)) : (D.snoc g).last = g :=
  snoc_gate_last D g

@[simp] theorem snoc_init_last (D : Dag n (s + 1)) : D.init.snoc D.last = D := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact snoc_gate_last _ _
  · exact snoc_gate_castSucc _ _ i

/-- The old wires of `snoc` keep their values. -/
@[simp] theorem val_snoc_castSucc (D : Dag n s) (g : KGate (n + s)) (x : Fin n → Bool)
    (w : Fin (n + s)) : (D.snoc g).val x w.castSucc = D.val x w := by
  have h := val_take (D.snoc g) s (Nat.le_succ s) x w
  rw [show (D.snoc g).take s (Nat.le_succ s) = D from init_snoc D g] at h
  exact h.symm

/-- The new wire of `snoc` is the new gate on the old values. -/
@[simp] theorem val_snoc_last (D : Dag n s) (g : KGate (n + s)) (x : Fin n → Bool) :
    (D.snoc g).val x (Fin.last (n + s)) = g.eval (D.val x) := by
  have h := (D.snoc g).val_natAdd x (Fin.last s)
  rw [snoc_gate_last] at h
  exact Eq.trans h (KGate.eval_congr fun a _ => val_snoc_castSucc D g x a)

/-- **Snoc induction** on dags. -/
theorem snocInduction {motive : ∀ s, Dag n s → Prop} (hnil : motive 0 nil)
    (hsnoc : ∀ s (D : Dag n s) (g : KGate (n + s)), motive s D → motive (s + 1) (D.snoc g)) :
    ∀ s (D : Dag n s), motive s D := by
  intro s
  induction s with
  | zero =>
    intro D
    have : D = nil := by ext i; exact i.elim0
    exact this ▸ hnil
  | succ s ih =>
    intro D
    have := hsnoc s D.init D.last (ih D.init)
    rwa [snoc_init_last] at this

/-! ## Gatewise maps -/

/-- Rewrite every gate in place (the rewrite may depend on the gate index). -/
def mapIdx (D : Dag n s) (f : (i : Fin s) → KGate (n + i) → KGate (n + i)) : Dag n s :=
  ⟨fun i => f i (D.gate i)⟩

@[simp] theorem mapIdx_gate (D : Dag n s) (f : (i : Fin s) → KGate (n + i) → KGate (n + i))
    (i : Fin s) : (D.mapIdx f).gate i = f i (D.gate i) := rfl

/-! ## Pass: replace NOT by a constant; the sandwich -/

/-- Every NOT gate becomes the constant `b`. -/
def constNot (D : Dag n s) (b : Bool) : Dag n s := D.mapIdx fun _ g => g.constNot b

@[simp] theorem constNot_gate (D : Dag n s) (b : Bool) (i : Fin s) :
    (D.constNot b).gate i = (D.gate i).constNot b := rfl

theorem constNot_notFree (D : Dag n s) (b : Bool) : (D.constNot b).NotFree :=
  fun i => KGate.isNot_constNot b (D.gate i)

theorem constNot_of_notFree (D : Dag n s) (b : Bool) (hD : D.NotFree) : D.constNot b = D := by
  ext i
  exact KGate.constNot_of_isNot_false b (hD i)

theorem constNot_mono (D : Dag n s) (b : Bool) (hD : D.MonoOffNot) : (D.constNot b).Mono :=
  fun i => KGate.opMono_constNot b (hD i)

theorem _root_.PEqualNP.Kernel.KGate.constNot_false_le {k : ℕ} (g : KGate k)
    (hg : g.isNot = false → OpMono g.op)
    {v v' : Fin k → Bool} (h : v ≤ v') : (g.constNot false).eval v ≤ g.eval v' := by
  cases hn : g.isNot
  · rw [KGate.constNot_of_isNot_false false hn]
    exact KGate.eval_mono (hg hn) fun a _ => h a
  · rw [KGate.constNot_of_isNot false hn, KGate.eval_const]
    exact Bool.false_le _

theorem _root_.PEqualNP.Kernel.KGate.le_constNot_true {k : ℕ} (g : KGate k)
    (hg : g.isNot = false → OpMono g.op)
    {v v' : Fin k → Bool} (h : v ≤ v') : g.eval v ≤ (g.constNot true).eval v' := by
  cases hn : g.isNot
  · rw [KGate.constNot_of_isNot_false true hn]
    exact KGate.eval_mono (hg hn) fun a _ => h a
  · rw [KGate.constNot_of_isNot true hn, KGate.eval_const]
    exact Bool.le_true _

/-- **Sandwich** `C0 ≤ C ≤ C1`, for any number of NOT gates (the other gates monotone, any
fan-in), in the monotone form: the lower world at a smaller input is below the circuit, which is
below the upper world at a larger input. -/
theorem constNot_false_le (D : Dag n s) (hD : D.MonoOffNot) {x y : Fin n → Bool} (hxy : x ≤ y)
    (w : Fin (n + s)) : (D.constNot false).val x w ≤ D.val y w :=
  val_le_val _ _ hxy (fun i _ _ hv => (D.gate i).constNot_false_le (hD i) hv) w

theorem le_constNot_true (D : Dag n s) (hD : D.MonoOffNot) {x y : Fin n → Bool} (hxy : x ≤ y)
    (w : Fin (n + s)) : D.val x w ≤ (D.constNot true).val y w :=
  val_le_val _ _ hxy (fun i _ _ hv => (D.gate i).le_constNot_true (hD i) hv) w

theorem sandwich (D : Dag n s) (hD : D.MonoOffNot) (x : Fin n → Bool) (w : Fin (n + s)) :
    (D.constNot false).val x w ≤ D.val x w ∧ D.val x w ≤ (D.constNot true).val x w :=
  ⟨D.constNot_false_le hD le_rfl w, D.le_constNot_true hD le_rfl w⟩

/-- If every NOT gate of `D` has value `b` at `x`, then `D` and `D.constNot b` agree at `x`. -/
theorem val_constNot_of_eq (D : Dag n s) (b : Bool) (x : Fin n → Bool)
    (h : ∀ i, (D.gate i).isNot = true → D.val x (Fin.natAdd n i) = b) (w : Fin (n + s)) :
    (D.constNot b).val x w = D.val x w := by
  revert w
  refine wire_induction (fun j => by simp) (fun i ih => ?_)
  have hi := h i
  rw [val_natAdd] at hi ⊢
  rw [val_natAdd, constNot_gate]
  have e : (fun a => (D.constNot b).val x (lift i a)) = fun a => D.val x (lift i a) :=
    funext ih
  rw [e]
  cases hn : (D.gate i).isNot
  · rw [KGate.constNot_of_isNot_false b hn]
  · rw [KGate.constNot_of_isNot b hn, KGate.eval_const]
    exact (hi hn).symm

/-- **One NOT: two worlds.** With at most one NOT gate, at every input the circuit coincides
(on all wires) with the lower world `constNot false` or with the upper world `constNot true`. -/
theorem val_eq_constNot_of_atMostOne (D : Dag n s)
    (h1 : ∀ i j, (D.gate i).isNot = true → (D.gate j).isNot = true → i = j)
    (x : Fin n → Bool) :
    (∀ w, (D.constNot false).val x w = D.val x w) ∨
      (∀ w, (D.constNot true).val x w = D.val x w) := by
  by_cases hex : ∃ i, (D.gate i).isNot = true
  · obtain ⟨i, hi⟩ := hex
    have key : ∀ b, D.val x (Fin.natAdd n i) = b → ∀ w, (D.constNot b).val x w = D.val x w :=
      fun b hb => D.val_constNot_of_eq b x fun j hj => h1 i j hi hj ▸ hb
    cases hb : D.val x (Fin.natAdd n i)
    · exact Or.inl (key false hb)
    · exact Or.inr (key true hb)
  · left
    rw [D.constNot_of_notFree false fun i => by
      cases h : (D.gate i).isNot
      · rfl
      · exact absurd ⟨i, h⟩ hex]
    exact fun _ => rfl

/-! ## Pass: mask, closed sets, cones -/

/-- `K` (a set of wires) is closed under reads: a gate in `K` reads only wires in `K`. -/
def Closed (D : Dag n s) (K : Fin (n + s) → Prop) : Prop :=
  ∀ i : Fin s, K (Fin.natAdd n i) → ∀ a ∈ (D.gate i).reads, K (lift i a)

/-- Gates outside `K` become the constant `false`; no reindexing. -/
def mask (D : Dag n s) (K : Fin (n + s) → Prop) [DecidablePred K] : Dag n s :=
  D.mapIdx fun i g => if K (Fin.natAdd n i) then g else KGate.const false

theorem mask_gate (D : Dag n s) (K : Fin (n + s) → Prop) [DecidablePred K] (i : Fin s) :
    (D.mask K).gate i = if K (Fin.natAdd n i) then D.gate i else KGate.const false := rfl

/-- Masking with a closed set does not change the wires in the set. -/
theorem val_mask (D : Dag n s) (K : Fin (n + s) → Prop) [DecidablePred K] (hK : D.Closed K)
    (x : Fin n → Bool) (w : Fin (n + s)) (hw : K w) : (D.mask K).val x w = D.val x w := by
  have := agree_off₂ (D.mask K) D x x (fun w => ¬ K w) (fun _ _ => rfl)
    (fun i hi => by
      have hi' : K (Fin.natAdd n i) := not_not.mp hi
      have e : (D.mask K).gate i = D.gate i := by simp [mask_gate, hi']
      exact ⟨e, fun a ha => not_not.mpr (hK i hi' a (e ▸ ha))⟩) w (not_not.mpr hw)
  exact this

/-- A masked-away gate is `false`. -/
theorem val_mask_out (D : Dag n s) (K : Fin (n + s) → Prop) [DecidablePred K]
    (x : Fin n → Bool) (i : Fin s) (hi : ¬ K (Fin.natAdd n i)) :
    (D.mask K).val x (Fin.natAdd n i) = false := by
  rw [val_natAdd, mask_gate]; simp [hi]

theorem mask_true (D : Dag n s) : D.mask (fun _ => True) = D := by
  ext i; simp [mask_gate]

/-- The wires of a closed set depend only on the inputs in the set. -/
theorem Closed.val_congr {D : Dag n s} {K : Fin (n + s) → Prop} (hK : D.Closed K)
    {x y : Fin n → Bool} (hxy : ∀ j : Fin n, K (Fin.castAdd s j) → x j = y j)
    (w : Fin (n + s)) (hw : K w) : D.val x w = D.val y w :=
  agree_off D x y (fun w => ¬ K w) (fun j hj => hxy j (not_not.mp hj))
    (fun i hi a ha => not_not.mpr (hK i (not_not.mp hi) a ha)) w (not_not.mpr hw)

/-- Wire `u` reads wire `v` directly. -/
def Reads (D : Dag n s) (u v : Fin (n + s)) : Prop :=
  ∃ i : Fin s, u = Fin.natAdd n i ∧ ∃ a ∈ (D.gate i).reads, v = lift i a

/-- The cone of a set `O` of wires: everything reachable from `O` along reads. -/
def cone (D : Dag n s) (O : Fin (n + s) → Prop) (w : Fin (n + s)) : Prop :=
  ∃ o, O o ∧ Relation.ReflTransGen D.Reads o w

theorem subset_cone (D : Dag n s) (O : Fin (n + s) → Prop) {o : Fin (n + s)} (ho : O o) :
    D.cone O o := ⟨o, ho, Relation.ReflTransGen.refl⟩

theorem cone_closed (D : Dag n s) (O : Fin (n + s) → Prop) : D.Closed (D.cone O) := by
  rintro i ⟨o, ho, hr⟩ a ha
  exact ⟨o, ho, hr.tail ⟨i, rfl, a, ha, rfl⟩⟩

/-- The cone is the least closed set containing `O`. -/
theorem cone_subset (D : Dag n s) {O K : Fin (n + s) → Prop} (hK : D.Closed K)
    (hO : ∀ o, O o → K o) : ∀ w, D.cone O w → K w := by
  rintro w ⟨o, ho, hr⟩
  induction hr with
  | refl => exact hO o ho
  | tail _ hbc ih =>
    obtain ⟨i, rfl, a, ha, rfl⟩ := hbc
    exact hK i ih a ha

theorem cone_mono (D : Dag n s) {O O' : Fin (n + s) → Prop} (h : ∀ o, O o → O' o) :
    ∀ w, D.cone O w → D.cone O' w :=
  fun _ ⟨o, ho, hr⟩ => ⟨o, h o ho, hr⟩

/-- A wire in a cone is not above every output: cones only go down. -/
theorem cone_le (D : Dag n s) {O : Fin (n + s) → Prop} {w : Fin (n + s)} (hw : D.cone O w) :
    ∃ o, O o ∧ w ≤ o := by
  obtain ⟨o, ho, hr⟩ := hw
  refine ⟨o, ho, ?_⟩
  induction hr with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨i, rfl, a, _, rfl⟩ := hbc
    exact le_trans (le_of_lt (show (lift i a).1 < n + i.1 from a.2)) ih

/-- Masking with the cone of the outputs keeps the outputs (and their whole cone). -/
theorem val_mask_cone (D : Dag n s) (O : Fin (n + s) → Prop) [DecidablePred (D.cone O)]
    (x : Fin n → Bool) (w : Fin (n + s)) (hw : D.cone O w) :
    (D.mask (D.cone O)).val x w = D.val x w :=
  D.val_mask _ (D.cone_closed O) x w hw

/-- The cone of the outputs depends only on the inputs in the cone. -/
theorem val_congr_cone (D : Dag n s) (O : Fin (n + s) → Prop) {x y : Fin n → Bool}
    (hxy : ∀ j : Fin n, D.cone O (Fin.castAdd s j) → x j = y j) (w : Fin (n + s))
    (hw : D.cone O w) : D.val x w = D.val y w :=
  (D.cone_closed O).val_congr hxy w hw

/-! ## Pass: restriction to a subcube -/

/-- A partial assignment of the inputs, seen as a partial assignment of the wires below `k`
gates (gate wires are never fixed). -/
def wireρ (ρ : Fin n → Option Bool) (k : ℕ) (a : Fin (n + k)) : Option Bool :=
  if h : a.1 < n then ρ ⟨a.1, h⟩ else none

/-- The input `x` with the fixed coordinates overwritten. -/
def override (ρ : Fin n → Option Bool) (x : Fin n → Bool) (j : Fin n) : Bool :=
  (ρ j).getD (x j)

theorem override_of_none {ρ : Fin n → Option Bool} {j : Fin n} (h : ρ j = none)
    (x : Fin n → Bool) : override ρ x j = x j := by simp [override, h]

theorem override_of_some {ρ : Fin n → Option Bool} {j : Fin n} {c : Bool} (h : ρ j = some c)
    (x : Fin n → Bool) : override ρ x j = c := by simp [override, h]

/-- **Restriction.** Fix the inputs `j` with `ρ j = some c` to `c`: every gate is simplified in
place (`KGate.subst`), so the result has the same number of gates, the same operations and
fan-ins, and no gate reads a fixed input. -/
def restrict (D : Dag n s) (ρ : Fin n → Option Bool) : Dag n s :=
  D.mapIdx fun i g => g.subst (wireρ ρ i)

@[simp] theorem restrict_gate (D : Dag n s) (ρ : Fin n → Option Bool) (i : Fin s) :
    (D.restrict ρ).gate i = (D.gate i).subst (wireρ ρ i) := rfl

/-- No gate of a restricted dag reads a fixed input. -/
theorem restrict_reads (D : Dag n s) (ρ : Fin n → Option Bool) (i : Fin s) (a : Fin (n + i))
    (ha : a ∈ ((D.restrict ρ).gate i).reads) (j : Fin n) (hj : lift i a = Fin.castAdd s j) :
    ρ j = none := by
  have h := (KGate.mem_reads_subst ha).1
  have hlt : a.1 < n := by
    have := congrArg Fin.val hj; simp at this; omega
  have : (⟨a.1, hlt⟩ : Fin n) = j := Fin.ext (by simpa using congrArg Fin.val hj)
  simpa [wireρ, hlt, this] using h

theorem restrict_notFree (D : Dag n s) (ρ : Fin n → Option Bool) (hD : D.NotFree) :
    (D.restrict ρ).NotFree := fun i => KGate.isNot_subst _ (hD i)

theorem restrict_mono (D : Dag n s) (ρ : Fin n → Option Bool) (hD : D.Mono) :
    (D.restrict ρ).Mono := fun i => hD i

/-- On inputs that respect the assignment, restriction changes no wire. -/
theorem val_restrict (D : Dag n s) (ρ : Fin n → Option Bool) (x : Fin n → Bool)
    (hx : ∀ j c, ρ j = some c → x j = c) (w : Fin (n + s)) :
    (D.restrict ρ).val x w = D.val x w := by
  revert w
  refine wire_induction (fun j => by simp) (fun i ih => ?_)
  rw [val_natAdd, val_natAdd, restrict_gate]
  have e : (fun a => (D.restrict ρ).val x (lift i a)) = fun a => D.val x (lift i a) :=
    funext ih
  rw [e]
  refine KGate.eval_subst _ _ _ fun a _ c hc => ?_
  unfold wireρ at hc
  split at hc
  · next h =>
    have : lift i a = Fin.castAdd s ⟨a.1, h⟩ := Fin.ext rfl
    rw [this, val_castAdd]
    exact hx _ c hc
  · exact absurd hc (by simp)

/-- A restricted dag ignores the fixed inputs (on every wire except those fixed inputs). -/
theorem val_restrict_congr (D : Dag n s) (ρ : Fin n → Option Bool) {x y : Fin n → Bool}
    (hxy : ∀ j, ρ j = none → x j = y j) (w : Fin (n + s))
    (hw : ∀ j, w = Fin.castAdd s j → ρ j = none) :
    (D.restrict ρ).val x w = (D.restrict ρ).val y w := by
  refine agree_off (D.restrict ρ) x y (fun w => ∃ j, w = Fin.castAdd s j ∧ ρ j ≠ none)
    (fun j hj => hxy j ?_) (fun i _ a ha => ?_) w ?_
  · by_contra h; exact hj ⟨j, rfl, h⟩
  · rintro ⟨j, hj, hne⟩; exact hne (D.restrict_reads ρ i a ha j hj)
  · rintro ⟨j, hj, hne⟩; exact hne (hw j hj)

/-- **Restriction computes the function on the subcube**: at every unfixed wire, the
restricted dag on `x` is the original dag on `x` with the fixed inputs overwritten. -/
theorem val_restrict_override (D : Dag n s) (ρ : Fin n → Option Bool) (x : Fin n → Bool)
    (w : Fin (n + s)) (hw : ∀ j, w = Fin.castAdd s j → ρ j = none) :
    (D.restrict ρ).val x w = D.val (override ρ x) w := by
  rw [← D.val_restrict ρ (override ρ x) (fun j c hc => override_of_some hc x) w]
  exact D.val_restrict_congr ρ (fun j hj => (override_of_none hj x).symm) w hw

theorem val_restrict_gate (D : Dag n s) (ρ : Fin n → Option Bool) (x : Fin n → Bool)
    (i : Fin s) : (D.restrict ρ).val x (Fin.natAdd n i) = D.val (override ρ x) (Fin.natAdd n i) :=
  D.val_restrict_override ρ x _ fun j hj => by
    have := congrArg Fin.val hj; simp at this; omega

/-! ### The subcube `{x ≥ z}` -/

/-- The assignment fixing to `true` the inputs where `z` is `true`. -/
def geρ (z : Fin n → Bool) (j : Fin n) : Option Bool := if z j then some true else none

/-- Restriction to the subcube `{x | z ≤ x}`. -/
def restrictGE (D : Dag n s) (z : Fin n → Bool) : Dag n s := D.restrict (geρ z)

theorem override_geρ (z x : Fin n → Bool) : override (geρ z) x = x ⊔ z := by
  funext j
  cases hz : z j <;> simp [override, geρ, hz]

/-- On the subcube, `restrictGE` changes no wire. -/
theorem val_restrictGE (D : Dag n s) (z x : Fin n → Bool) (hzx : z ≤ x) (w : Fin (n + s)) :
    (D.restrictGE z).val x w = D.val x w :=
  D.val_restrict _ x (fun j c hc => by
    unfold geρ at hc
    split at hc
    · next h =>
      have h1 : x j = true := by
        have := hzx j; rw [h] at this; exact le_antisymm (Bool.le_true _) this
      rw [h1]; exact Option.some.inj hc
    · exact absurd hc (by simp)) w

/-- Everywhere, a gate of `restrictGE z` at `x` is the original gate at `x ⊔ z`. -/
theorem val_restrictGE_gate (D : Dag n s) (z x : Fin n → Bool) (i : Fin s) :
    (D.restrictGE z).val x (Fin.natAdd n i) = D.val (x ⊔ z) (Fin.natAdd n i) := by
  rw [restrictGE, val_restrict_gate, override_geρ]

/-- Gates of `restrictGE z` do not look at the inputs fixed by `z`. -/
theorem val_restrictGE_congr (D : Dag n s) (z : Fin n → Bool) {x y : Fin n → Bool}
    (hxy : ∀ j, z j = false → x j = y j) (i : Fin s) :
    (D.restrictGE z).val x (Fin.natAdd n i) = (D.restrictGE z).val y (Fin.natAdd n i) := by
  rw [val_restrictGE_gate, val_restrictGE_gate]
  congr 1
  funext j
  cases hz : z j
  · simp [hz, hxy j hz]
  · simp [hz]

theorem restrictGE_notFree (D : Dag n s) (z : Fin n → Bool) (hD : D.NotFree) :
    (D.restrictGE z).NotFree := D.restrict_notFree _ hD

theorem restrictGE_mono (D : Dag n s) (z : Fin n → Bool) (hD : D.Mono) :
    (D.restrictGE z).Mono := D.restrict_mono _ hD

/-! ## Comparing a wire with a function on a set of inputs -/

/-- The OR of the inputs in `S`. -/
def orOf (S : Finset (Fin n)) (x : Fin n → Bool) : Bool := decide (∃ v ∈ S, x v = true)

theorem orOf_mono (S : Finset (Fin n)) {x y : Fin n → Bool} (hxy : x ≤ y) :
    orOf S x ≤ orOf S y := by
  rw [Bool.le_iff_imp]
  simp only [orOf, decide_eq_true_eq]
  rintro ⟨v, hv, hx⟩
  exact ⟨v, hv, le_antisymm (Bool.le_true _) (hx ▸ hxy v)⟩

/-- Wire `w` computes `f` on the set `A` of inputs. -/
def ComputesOn (D : Dag n s) (A : (Fin n → Bool) → Prop) (w : Fin (n + s))
    (f : (Fin n → Bool) → Bool) : Prop := ∀ x, A x → D.val x w = f x

/-- **A gate on the subcube `{x ≥ z}`** computes `f` there iff the same gate of `restrictGE z`
computes `x ↦ f (x ⊔ z)` everywhere. -/
theorem computesOn_ge_iff (D : Dag n s) (z : Fin n → Bool) (i : Fin s)
    (f : (Fin n → Bool) → Bool) :
    D.ComputesOn (fun x => z ≤ x) (Fin.natAdd n i) f ↔
      ∀ x, (D.restrictGE z).val x (Fin.natAdd n i) = f (x ⊔ z) := by
  constructor
  · intro h x
    rw [val_restrictGE_gate]
    exact h _ le_sup_right
  · intro h x hzx
    have := h x
    rwa [val_restrictGE_gate, sup_eq_left.mpr hzx] at this

/-- If the wires in a set agree off `Bad`-free cones: two dags with the same gates on a closed
set `K` agree on `K` (the two-circuit form of `Closed.val_congr`). -/
theorem Closed.val_congr₂ {D D' : Dag n s} {K : Fin (n + s) → Prop} (hK : D.Closed K)
    (hDD' : ∀ i : Fin s, K (Fin.natAdd n i) → D.gate i = D'.gate i)
    {x y : Fin n → Bool} (hxy : ∀ j : Fin n, K (Fin.castAdd s j) → x j = y j)
    (w : Fin (n + s)) (hw : K w) : D.val x w = D'.val y w :=
  agree_off₂ D D' x y (fun w => ¬ K w) (fun j hj => hxy j (not_not.mp hj))
    (fun i hi => ⟨hDD' i (not_not.mp hi), fun a ha => not_not.mpr (hK i (not_not.mp hi) a ha)⟩)
    w (not_not.mpr hw)

end Dag

/-! ## Snoc evaluators (list circuits with no well-formedness hypothesis)

W951 evaluates a `List` of gates by a fold; the only fact about that evaluator its structural
lemmas use is the snoc law `V (gs ++ [g]) i = if i = n + gs.length then ev g (V gs) else V gs i`.
The transfer lemma below is `Dag.val_rel` for such an evaluator: it needs no hypothesis on the
gates (no fan-in bound, no scoping), so it applies where the `Dag` bridge does not. -/

/-- The snoc law of a list evaluator `V` on `n` inputs with gate semantics `ev`. -/
def SnocLaw {α : Type*} (n : ℕ) (ev : α → (ℕ → Bool) → Bool) (V : List α → ℕ → Bool) : Prop :=
  ∀ (gs : List α) (g : α) (i : ℕ),
    V (gs ++ [g]) i = if i = n + gs.length then ev g (V gs) else V gs i

/-- **Transfer for snoc evaluators.** Rewrite the gates positionwise by `f`. If every rewritten
gate whose wire is in `P` computes the same value from wire values that agree on `P`, then the
rewritten circuit agrees with the original on `P`. -/
theorem SnocLaw.mapIdx_congr {α : Type*} {n : ℕ} {ev : α → (ℕ → Bool) → Bool}
    {V : List α → ℕ → Bool} (hV : SnocLaw n ev V) (f : ℕ → α → α) (P : ℕ → Prop) :
    ∀ gs : List α,
      (∀ (k : ℕ) (hk : k < gs.length), P (n + k) → ∀ v v' : ℕ → Bool,
        (∀ i, P i → v i = v' i) → ev (f k gs[k]) v = ev gs[k] v') →
      ∀ i, P i → V (gs.mapIdx f) i = V gs i := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ i _; rfl
  | append_singleton gs g ih =>
    intro hf i hi
    have ih' := ih fun k hk hP v v' hv => by
      have := hf k (by simp; omega) hP v v' hv
      rwa [List.getElem_append_left hk] at this
    rw [List.mapIdx_append, List.mapIdx_singleton, hV, hV, List.length_mapIdx, Nat.zero_add]
    split_ifs with h
    · have := hf gs.length (by simp) (h ▸ hi) _ _ ih'
      simpa using this
    · exact ih' i hi

end PEqualNP.Kernel
