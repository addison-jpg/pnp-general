-- Superseded by one-not/lean/PEqualNP/Kernel (same Dag, exact-count passes); see coord. No new work here.
import Mathlib.Data.Fin.Basic
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Kernel.Circuit: well-scoped fan-in-two circuits

`Defs/CircuitLowerBounds.lean` states circuits as `List Gate` with `List.getD _ false`, so every
proof pays for a wire that does not exist. Here a gate reads `Fin (n + i)`: only the `n` inputs
and the `i` gates before it, by type. `Dag n s` has `n` inputs, `s` gates and no junk case.

Nothing in `Defs/` changes. This file proves one bridge: `Dag.toCircuit` has the same size and
the same value as the `Defs` circuit it names.
-/

namespace PEqualNP.Kernel

open PEqualNP.CircuitLowerBounds

/-- A fan-in-two gate that can read any of `m` earlier wires. -/
inductive DGate (m : ℕ) where
  | and (a b : Fin m)
  | or (a b : Fin m)
  | not (a : Fin m)
  /-- A constant. It counts as a gate. -/
  | const (c : Bool)

/-- A circuit on `n` inputs with `s` gates. Gate `i` reads wires numbered below `n + i`. -/
structure Dag (n s : ℕ) where
  gate : (i : Fin s) → DGate (n + i)
  out : Fin (n + s)

variable {n s : ℕ}

/-- The value of a gate, given the value of each wire it may read. -/
def DGate.eval {m : ℕ} : DGate m → (Fin m → Bool) → Bool
  | .and a b, f => f a && f b
  | .or a b, f => f a || f b
  | .not a, f => !(f a)
  | .const c, _ => c

/-- The value of wire `k` on input `x`: an input bit, or a gate applied to earlier wires.
A number `k ≥ n + s` is no wire and reads `false`. -/
def Dag.val (D : Dag n s) (x : Fin n → Bool) (k : ℕ) : Bool :=
  if h : k < n then x ⟨k, h⟩ else
  if h2 : k - n < s then
    (D.gate ⟨k - n, h2⟩).eval fun a => D.val x a.val
  else false
termination_by k
decreasing_by
  have h3 : (⟨k - n, h2⟩ : Fin s).val = k - n := rfl
  have := a.isLt
  omega

/-- The value of the circuit: the value of its output wire. -/
def Dag.eval (D : Dag n s) (x : Fin n → Bool) : Bool := D.val x D.out.val

/-- The size of a circuit: its number of gates. -/
def Dag.size (_ : Dag n s) : ℕ := s

/-- The gate of the `Defs` circuit that a `DGate` stands for. -/
def DGate.toGate {m : ℕ} : DGate m → Gate
  | .and a b => ⟨GateOp.and, [a.val, b.val]⟩
  | .or a b => ⟨GateOp.or, [a.val, b.val]⟩
  | .not a => ⟨GateOp.not, [a.val]⟩
  | .const true => ⟨GateOp.and, []⟩
  | .const false => ⟨GateOp.or, []⟩

/-- The `Defs` circuit that a `Dag` stands for. -/
def Dag.toCircuit (D : Dag n s) : Circuit :=
  ⟨List.ofFn fun i : Fin s => (D.gate i).toGate, D.out.val⟩

theorem Dag.size_toCircuit (D : Dag n s) : D.toCircuit.size = D.size := by
  simp [Dag.toCircuit, Circuit.size, Dag.size]

/-- Every gate of `D.toCircuit` has fan-in at most two and is AND, OR or NOT. -/
theorem Dag.toCircuit_basis (D : Dag n s) :
    ∀ g ∈ D.toCircuit.gates,
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [Dag.toCircuit, List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  cases h : D.gate i with
  | const c => cases c <;> simp [DGate.toGate]
  | _ => simp [DGate.toGate]

/-- A gate's value, whichever way it is written. -/
private theorem toGate_eval {m : ℕ} (g : DGate m) (F : ℕ → Bool) :
    g.toGate.op.eval (g.toGate.inputs.map F) = g.eval fun a => F a.val := by
  cases g with
  | const c => cases c <;> simp [DGate.toGate, GateOp.eval, DGate.eval]
  | _ => simp [DGate.toGate, GateOp.eval, DGate.eval]

/-- Wire `n + j` is gate `j`. -/
private theorem val_gate (D : Dag n s) (x : Fin n → Bool) (j : ℕ) (hj : j < s) :
    D.val x (n + j) = (D.gate ⟨j, hj⟩).eval fun a => D.val x a.val := by
  have hk : ¬ (n + j < n) := by omega
  have hs : n + j - n < s := by omega
  have cong : ∀ i i' : Fin s, i.val = i'.val →
      (D.gate i).eval (fun a => D.val x a.val) = (D.gate i').eval (fun a => D.val x a.val) := by
    intro i i' h
    have := Fin.ext h
    subst this
    rfl
  rw [Dag.val.eq_1, dite_eq_right_of_eq_false (eq_false hk), dite_eq_left_of_eq_true (eq_true hs)]
  exact cong _ _ (by simp)

/-- Wire `k` is gate `j` when `k = n + j`. -/
private theorem val_gate' (D : Dag n s) (x : Fin n → Bool) (k j : ℕ) (hj : j < s)
    (hk : k = n + j) :
    D.val x k = (D.gate ⟨j, hj⟩).eval fun a => D.val x a.val := by
  subst hk
  exact val_gate D x j hj

/-- One step of the evaluation of `Defs`: the wire a gate adds, read off the wires so far. -/
private theorem step_eq (D : Dag n s) (x : Fin n → Bool) (j : ℕ) (hj : j < s)
    (w : List Bool) (hw : w = List.ofFn fun k : Fin (n + j) => D.val x k) :
    ((D.gate ⟨j, hj⟩).toGate.op.eval
      ((D.gate ⟨j, hj⟩).toGate.inputs.map fun i => w.getD i false)) = D.val x (n + j) := by
  rw [toGate_eval, val_gate D x j hj]
  congr 1
  funext a
  subst hw
  have := a.isLt
  simp [List.getD_eq_getElem?_getD, this]

/-- After the first `j` gates, the wire list is exactly the first `n + j` values of `D`. -/
private theorem wires_prefix (D : Dag n s) (x : Fin n → Bool) :
    ∀ j, j ≤ s →
      ((List.ofFn fun i : Fin s => (D.gate i).toGate).take j).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
        = List.ofFn fun k : Fin (n + j) => D.val x k := by
  intro j
  induction j with
  | zero =>
    intro _
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp only [List.take_zero, List.foldl_nil, List.getElem_ofFn]
      rw [Dag.val.eq_1, dite_eq_left_of_eq_true (eq_true hi)]
  | succ j ih =>
    intro hj
    have hjs : j < s := by omega
    have htake : (List.ofFn fun i : Fin s => (D.gate i).toGate).take (j + 1)
        = (List.ofFn fun i : Fin s => (D.gate i).toGate).take j
          ++ [(D.gate ⟨j, hjs⟩).toGate] := by
      rw [List.take_add_one]
      simp [hjs]
    rw [htake, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [step_eq D x j hjs _ rfl]
    apply List.ext_getElem
    · simp [Nat.add_assoc]
    · intro i h1 h2
      simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn,
        List.getElem_singleton]
      split_ifs with h
      · rfl
      · congr 1
        simp at h1
        omega

/-- The bridge: `D.toCircuit` computes what `D` computes. -/
theorem Dag.eval_toCircuit (D : Dag n s) (x : Fin n → Bool) :
    D.toCircuit.eval (List.ofFn x) = D.eval x := by
  have h := wires_prefix D x s le_rfl
  rw [List.take_of_length_le (by simp)] at h
  unfold Circuit.eval Circuit.wires Dag.toCircuit
  simp only
  rw [h]
  simp [Dag.eval, List.getD_eq_getElem?_getD, D.out.isLt]

/-- Move a gate to a scope of the same size. -/
def DGate.cast {m m' : ℕ} (h : m = m') : DGate m → DGate m'
  | .and a b => .and (Fin.cast h a) (Fin.cast h b)
  | .or a b => .or (Fin.cast h a) (Fin.cast h b)
  | .not a => .not (Fin.cast h a)
  | .const c => .const c

theorem DGate.eval_cast {m m' : ℕ} (h : m = m') (g : DGate m) (f : Fin m' → Bool) :
    (g.cast h).eval f = g.eval fun a => f (Fin.cast h a) := by
  cases g <;> rfl

/-- An input on `n + 1` wires, given by its first `n` bits and its last bit. -/
def snocIn (x : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else b

/-- Fix the last input to `b`. The input becomes a constant gate, placed first, and every
other wire keeps its number. Gates that read the constant are not removed here. -/
def Dag.restrict (D : Dag (n + 1) s) (b : Bool) : Dag n (s + 1) where
  gate := Fin.cases (motive := fun i : Fin (s + 1) => DGate (n + i)) (.const b)
    fun j => (D.gate j).cast (by simp [Fin.val_succ]; omega)
  out := Fin.cast (by omega) D.out

theorem Dag.size_restrict (D : Dag (n + 1) s) (b : Bool) : (D.restrict b).size = D.size + 1 := rfl

/-- The restriction computes `D` with the last input fixed, at every wire. -/
theorem Dag.val_restrict (D : Dag (n + 1) s) (b : Bool) (x : Fin n → Bool) :
    ∀ k, (D.restrict b).val x k = D.val (snocIn x b) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < n
    · rw [Dag.val.eq_1, dite_eq_left_of_eq_true (eq_true hk), Dag.val.eq_1,
        dite_eq_left_of_eq_true (eq_true (show k < n + 1 by omega))]
      simp [snocIn, hk]
    by_cases hkn : k = n
    · rw [hkn]
      have l0 : (D.restrict b).val x n = ((D.restrict b).gate ⟨0, by omega⟩).eval
          fun a => (D.restrict b).val x a.val := val_gate' _ x n 0 (by omega) (by omega)
      refine l0.trans (Eq.trans (show _ = b from rfl) ?_)
      rw [Dag.val.eq_1 D (snocIn x b) n,
        dite_eq_left_of_eq_true (eq_true (show n < n + 1 by omega))]
      simp [snocIn]
    by_cases hks : k < n + 1 + s
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + (j + 1) := ⟨k - n - 1, by omega⟩
      have hj : j < s := by omega
      have lhs := val_gate (D.restrict b) x (j + 1) (by omega)
      have rhs := val_gate' D (snocIn x b) (n + (j + 1)) j hj (by omega)
      rw [lhs, rhs]
      have hg : (D.restrict b).gate ⟨j + 1, by omega⟩
          = (D.gate ⟨j, hj⟩).cast (by simp; omega) := rfl
      rw [hg, DGate.eval_cast]
      congr 1
      funext a
      have h3 : (⟨j, hj⟩ : Fin s).val = j := rfl
      have h4 := a.isLt
      change (D.restrict b).val x a.val = D.val (snocIn x b) a.val
      exact ih a.val (by omega)
    · have e1 : ¬ (k - n < s + 1) := by omega
      have e2 : ¬ (k - (n + 1) < s) := by omega
      rw [Dag.val.eq_1, dite_eq_right_of_eq_false (eq_false hk),
        dite_eq_right_of_eq_false (eq_false e1), Dag.val.eq_1,
        dite_eq_right_of_eq_false (eq_false (show ¬ (k < n + 1) by omega)),
        dite_eq_right_of_eq_false (eq_false e2)]

/-- Fixing the last input: same size plus the constant, and the value of `D` on that input. -/
theorem Dag.eval_restrict (D : Dag (n + 1) s) (b : Bool) (x : Fin n → Bool) :
    (D.restrict b).eval x = D.eval (snocIn x b) := by
  unfold Dag.eval
  rw [Dag.val_restrict]
  rfl

end PEqualNP.Kernel
