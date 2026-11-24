import Mathlib.Tactic.Basic
/-!
# SearchCheck: Python finds a counterexample, Lean re-checks it in the kernel

Step 1+2 of `boards/tasks/lang-integration.md`, smallest end-to-end loop. A circuit is plain data
(`Gate` = opcode and two wires, `Circ` = n, sets, output wires, gate list). `tt` computes one `Nat` per
wire, bit r = value on input vector r (variable i = bit i of r), using `Nat.land/lor/xor` and the
all-ones mask for NOT (GMP in the kernel). `correctB` and `witnessCount` are Bool/Nat checkers on those
tables; the theorems are closed by `decide +kernel` (no `native_decide`, no `bv_decide`).

NOT PROVED HERE: this is a definitional check of the specific circuit. The bridge theorem
`tt.testBit r = Circuit.eval` (tie to the project's `Circuit`) is not proved here: that is step 2 on the
task board. So `correctB` means "the bit-parallel tables satisfy the spec", not yet a statement about
`Defs/BinaryCircuit`.

Wire conventions: wire i < n is input i, wire n+k is gate k. Op codes 0 = and, 1 = or, 2 = not (uses
only the first wire).
Witness gate g: exist set S, input Z zero on S, u ≠ u' in S with g(Z)=0, g(Z+e_u)=g(Z+e_u')=1.
Regenerate a data file: `python3 -I one-not/tools/search/to_lean.py FILE.json NAME`.
-/
namespace SearchCheck

structure Gate where
  op : Nat
  a : Nat
  b : Nat

structure Circ where
  n : Nat
  sets : List (List Nat)
  outs : List Nat
  gates : List Gate

/-- truth table of input i: bit r is bit i of r (rows r < 2^n). -/
def varTT (n i : Nat) : Nat :=
  (List.range (2^n)).foldr (fun r acc => (acc <<< 1) ||| (if r.testBit i then 1 else 0)) 0

/-- wire tables, newest wire LAST (`Array`), built by one fold over the gates. -/
def tt (full : Nat) (ws : List Nat) (gs : List Gate) : List Nat :=
  (gs.foldl (fun (w : Array Nat) g =>
    let x := w.getD g.a 0
    let y := w.getD g.b 0
    w.push (match g.op with
      | 0 => Nat.land x y
      | 1 => Nat.lor x y
      | _ => Nat.xor full x)) ws.toArray).toList

def Circ.tables (C : Circ) : Array Nat :=
  let full := 2^(2^C.n) - 1
  (tt full ((List.range C.n).map (varTT C.n)) C.gates).toArray

/-- every output wire equals the OR of the inputs of its set, on all 2^n inputs -/
def correctB (C : Circ) : Bool :=
  let T := C.tables
  let ins := (List.range C.n).map (varTT C.n)
  (C.sets.zip C.outs).all fun (S, o) =>
    T.getD o 0 == S.foldl (fun acc u => Nat.lor acc (ins.getD u 0)) 0

/-- does gate table `t` have a witness (S, Z, u, u') -/
def hasWitness (n : Nat) (sets : List (List Nat)) (t : Nat) : Bool :=
  sets.any fun S =>
    (List.range (2^n)).any fun r =>
      (S.all fun s => !r.testBit s) && !t.testBit r &&
      (S.filter fun u => t.testBit (Nat.lor r (2^u))).length ≥ 2

def witnessCount (C : Circ) : Nat :=
  let T := C.tables.toList.drop C.n
  (T.filter (hasWitness C.n C.sets)).length

def t4 : Circ := ⟨7, [[0, 1, 2, 3], [0, 4, 5, 6]], [39, 73], [⟨1, 0, 0⟩, ⟨1, 7, 0⟩, ⟨0, 7, 8⟩, ⟨0, 9, 5⟩, ⟨0, 4, 4⟩, ⟨0, 10, 11⟩, ⟨0, 0, 12⟩, ⟨1, 0, 13⟩, ⟨0, 12, 7⟩, ⟨1, 14, 12⟩, ⟨0, 16, 6⟩, ⟨1, 16, 17⟩, ⟨1, 18, 0⟩, ⟨0, 16, 19⟩, ⟨0, 2, 0⟩, ⟨1, 2, 21⟩, ⟨0, 22, 7⟩, ⟨0, 14, 2⟩, ⟨2, 19, 19⟩, ⟨1, 20, 20⟩, ⟨0, 16, 24⟩, ⟨1, 26, 19⟩, ⟨1, 19, 12⟩, ⟨0, 16, 26⟩, ⟨1, 10, 30⟩, ⟨1, 31, 26⟩, ⟨0, 32, 23⟩, ⟨1, 33, 27⟩, ⟨1, 34, 1⟩, ⟨1, 32, 31⟩, ⟨1, 36, 1⟩, ⟨1, 37, 2⟩, ⟨1, 38, 3⟩, ⟨0, 0, 0⟩, ⟨0, 0, 26⟩, ⟨0, 29, 41⟩, ⟨0, 42, 15⟩, ⟨1, 43, 20⟩, ⟨0, 43, 44⟩, ⟨0, 45, 39⟩, ⟨1, 43, 28⟩, ⟨1, 47, 46⟩, ⟨0, 48, 26⟩, ⟨1, 48, 49⟩, ⟨0, 50, 35⟩, ⟨1, 51, 32⟩, ⟨0, 52, 24⟩, ⟨0, 29, 40⟩, ⟨1, 51, 53⟩, ⟨0, 13, 24⟩, ⟨1, 14, 34⟩, ⟨0, 14, 57⟩, ⟨0, 58, 56⟩, ⟨1, 59, 4⟩, ⟨1, 60, 5⟩, ⟨2, 61, 61⟩, ⟨2, 6, 6⟩, ⟨0, 62, 45⟩, ⟨0, 62, 64⟩, ⟨0, 65, 55⟩, ⟨1, 62, 66⟩, ⟨0, 63, 14⟩, ⟨1, 63, 68⟩, ⟨1, 69, 54⟩, ⟨0, 70, 25⟩, ⟨0, 67, 71⟩, ⟨2, 72, 72⟩]⟩
theorem t4_correct : correctB t4 = true := by decide +kernel
theorem t4_witness : witnessCount t4 = 5 := by decide +kernel
#print axioms t4_correct
#print axioms t4_witness
theorem t4_below_base : witnessCount t4 < 6 := by rw [t4_witness]; decide
end SearchCheck
