/-!
# asteroid, Lean version: the checkers, with no library behind them

The executable `asteroid` must not link Mathlib, and the project's checkers live in files that
import it (`W951/SearchCheck.lean`, `W951/Asteroid.lean`, `W951/AsteroidCheap.lean`). So the
checkers are written here a second time, importing nothing, as functions of the plain data of a
circuit: the number of inputs, the sets, the output wires, the gate list, and the three fields of a
gate as functions `op a b : γ → Nat`. Written this way each one is the original with its structure
taken apart, and `AsteroidLang/CoreEq.lean` proves each equal to the original by `rfl`. Nothing is
trusted twice.

Conventions (as in `SearchCheck.lean`): wire `i < n` is input `i`, wire `n + k` is gate `k`; op
code 0 = and, 1 = or, anything else = not (first wire only). A table is one `Nat` per wire, bit `r`
= the value of the wire on the input whose bit `i` is input `i`.
-/
namespace AsteroidLang.Core

/-- truth table of input `i` -/
def varTT (n i : Nat) : Nat :=
  (List.range (2^n)).foldr (fun r acc => (acc <<< 1) ||| (if r.testBit i then 1 else 0)) 0

/-- wire tables, built by one fold over the gates -/
def tt {γ : Type} (op a b : γ → Nat) (full : Nat) (ws : List Nat) (gs : List γ) : List Nat :=
  (gs.foldl (fun (w : Array Nat) g =>
    let x := w.getD (a g) 0
    let y := w.getD (b g) 0
    w.push (match op g with
      | 0 => Nat.land x y
      | 1 => Nat.lor x y
      | _ => Nat.xor full x)) ws.toArray).toList

/-- one table per wire: the inputs, then the gates -/
def tables {γ : Type} (n : Nat) (gates : List γ) (op a b : γ → Nat) : Array Nat :=
  let full := 2^(2^n) - 1
  (tt op a b full ((List.range n).map (varTT n)) gates).toArray

/-- every output wire equals the OR of the inputs of its set, on all `2^n` inputs -/
def correctB {γ : Type} (n : Nat) (sets : List (List Nat)) (outs : List Nat) (gates : List γ)
    (op a b : γ → Nat) : Bool :=
  let T := tables n gates op a b
  let ins := (List.range n).map (varTT n)
  (sets.zip outs).all fun (S, o) =>
    T.getD o 0 == S.foldl (fun acc u => Nat.lor acc (ins.getD u 0)) 0

/-- does the table `t` have a witness (a set, a zero point of it, two of its atoms) -/
def hasWitness (n : Nat) (sets : List (List Nat)) (t : Nat) : Bool :=
  sets.any fun S =>
    (List.range (2^n)).any fun r =>
      (S.all fun s => !r.testBit s) && !t.testBit r &&
      (S.filter fun u => t.testBit (Nat.lor r (2^u))).length ≥ 2

/-- the number of gates, of any type, with a witness -/
def witnessCount {γ : Type} (n : Nat) (sets : List (List Nat)) (gates : List γ)
    (op a b : γ → Nat) : Nat :=
  let T := (tables n gates op a b).toList.drop n
  (T.filter (hasWitness n sets)).length

/-- does the table `t` have a witness above the cube `q` for a set avoiding `q` -/
def hasWitnessAt (n : Nat) (sets : List (List Nat)) (q t : Nat) : Bool :=
  sets.any fun S =>
    (S.all fun s => !q.testBit s) &&
    (List.range (2^n)).any fun r =>
      (Nat.land q r == q) && (S.all fun s => !r.testBit s) && !t.testBit r &&
      (S.filter fun u => t.testBit (Nat.lor r (2^u))).length ≥ 2

/-- the tables of the OR gates -/
def orTables {γ : Type} (n : Nat) (gates : List γ) (op a b : γ → Nat) : List Nat :=
  ((((tables n gates op a b).toList.drop n).zip gates).filter fun p => op p.2 == 1).map (·.1)

/-- the sum of (size − 1) over the sets that avoid the cube `q` -/
def baseAt (sets : List (List Nat)) (q : Nat) : Nat :=
  (sets.filter fun S => S.all fun s => !q.testBit s).foldl (fun acc S => acc + (S.length - 1)) 0

/-- how many of the tables `T` have a witness above the cube `q` -/
def orWitnessAtWith (n : Nat) (sets : List (List Nat)) (T : List Nat) (q : Nat) : Nat :=
  (T.filter (hasWitnessAt n sets q)).length

/-- the number of OR gates with a witness above the cube `q` -/
def orWitnessAt {γ : Type} (n : Nat) (sets : List (List Nat)) (gates : List γ) (op a b : γ → Nat)
    (q : Nat) : Nat :=
  orWitnessAtWith n sets (orTables n gates op a b) q

/-- slack at the cube `q` is at least `k` -/
def slackGe {γ : Type} (n : Nat) (sets : List (List Nat)) (gates : List γ) (op a b : γ → Nat)
    (q : Nat) (k : Int) : Bool :=
  decide ((orWitnessAt n sets gates op a b q : Int) - (baseAt sets q : Int) ≥ k)

/-- slack at the cube `q` is at most `k` -/
def slackLe {γ : Type} (n : Nat) (sets : List (List Nat)) (gates : List γ) (op a b : γ → Nat)
    (q : Nat) (k : Int) : Bool :=
  decide ((orWitnessAt n sets gates op a b q : Int) - (baseAt sets q : Int) ≤ k)

/-- base ≤ witnesses at every cube, for the given OR tables -/
def slackNonnegAllWith (n : Nat) (sets : List (List Nat)) (T : List Nat) : Bool :=
  (List.range (2^n)).all fun q => decide (baseAt sets q ≤ orWitnessAtWith n sets T q)

/-- slack is nonnegative at every cube -/
def slackNonnegAll {γ : Type} (n : Nat) (sets : List (List Nat)) (gates : List γ)
    (op a b : γ → Nat) : Bool :=
  slackNonnegAllWith n sets (orTables n gates op a b)

/-- every set is a list of distinct points below `n` -/
def setsOkB (n : Nat) (sets : List (List Nat)) : Bool :=
  sets.all fun S => decide S.Nodup && S.all fun u => decide (u < n)

/-- the number of NOT gates (op code `≥ 2`), counted by position -/
def notCount {γ : Type} (gates : List γ) (op : γ → Nat) (dflt : γ) : Nat :=
  ((List.range gates.length).filter fun k => decide (2 ≤ op (gates.getD k dflt))).length

/-- the side conditions of the theorem: well-formed sets, an output wire per set, at least one
gate, every set has at least 2 points, two sets share at most one point, at most one NOT gate -/
def hypsB {γ : Type} (n : Nat) (sets : List (List Nat)) (outs : List Nat) (gates : List γ)
    (op : γ → Nat) (dflt : γ) : Bool :=
  setsOkB n sets && decide (sets.length ≤ outs.length) && decide (0 < gates.length) &&
  (sets.all fun S => decide (2 ≤ S.length)) &&
  ((List.range sets.length).all fun i => (List.range sets.length).all fun j =>
    i == j || decide (((sets.getD i []).filter fun u => (sets.getD j []).contains u).length ≤ 1)) &&
  decide (notCount gates op dflt ≤ 1)

/-! ## The circuit of the executable -/

/-- a gate: an op code and two wires -/
structure Gate where
  op : Nat
  a : Nat
  b : Nat

/-- a circuit: `n` inputs, the sets, one output wire per set, the gates in order -/
structure Circ where
  n : Nat
  sets : List (List Nat)
  outs : List Nat
  gates : List Gate

namespace Circ
variable (C : Circ)
/-- every output wire computes the OR of its set (`correctB`) -/
def correct : Bool := correctB C.n C.sets C.outs C.gates Gate.op Gate.a Gate.b
/-- gates of any type with a witness at the empty cube (`witnessCount`) -/
def witness : Nat := witnessCount C.n C.sets C.gates Gate.op Gate.a Gate.b
/-- OR gates with a witness at the cube `q` (`orWitnessAt`) -/
def orWitness (q : Nat) : Nat := orWitnessAt C.n C.sets C.gates Gate.op Gate.a Gate.b q
/-- the sum of (size − 1) over the sets that avoid the cube `q` (`baseAt`) -/
def base (q : Nat) : Nat := baseAt C.sets q
/-- slack is nonnegative at every cube (`slackNonnegAll`) -/
def slackNonneg : Bool := slackNonnegAll C.n C.sets C.gates Gate.op Gate.a Gate.b
/-- the side conditions of the theorem (`hypsB`) -/
def hyps : Bool := hypsB C.n C.sets C.outs C.gates Gate.op ⟨0, 0, 0⟩
/-- the number of NOT gates (`notCount`) -/
def nots : Nat := notCount C.gates Gate.op ⟨0, 0, 0⟩
/-- every set is a list of distinct inputs (`setsOkB`) -/
def setsOk : Bool := setsOkB C.n C.sets
/-- the slack at every cube `q < 2^n`, with the OR tables computed once -/
def slackTable : List Int :=
  let T := orTables C.n C.gates Gate.op Gate.a Gate.b
  (List.range (2^C.n)).map fun q =>
    (orWitnessAtWith C.n C.sets T q : Int) - (baseAt C.sets q : Int)
end Circ

end AsteroidLang.Core
