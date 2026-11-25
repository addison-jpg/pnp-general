/-! One definition of circuit semantics, used for #eval, compiled code and kernel proofs. Core Lean only. -/
namespace LE
inductive Op | and | or | not | xor deriving DecidableEq, Repr
structure Gate where (op : Op) (a b : Nat) deriving DecidableEq, Repr
/-- straight-line circuit: wires 0..n-1 are inputs, gate i is wire n+i -/
abbrev Circuit := List Gate

/-- pointwise semantics (the *specification*) -/
def evalWires (gs : Circuit) (x : List Bool) : List Bool :=
  gs.foldl (fun w g =>
    let a := w.getD g.a false; let b := w.getD g.b false
    w ++ [match g.op with | .and => a && b | .or => a || b | .not => !a | .xor => a != b]) x
def eval (gs : Circuit) (x : List Bool) : Bool := (evalWires gs x).getLast?.getD false

/-- bit-parallel semantics: a wire is its whole truth table as a Nat (2^n bits); kernel has GMP for these -/
def varTT (n i : Nat) : Nat := -- truth table of x_i over 2^n rows
  (List.range (2^n)).foldl (fun acc r => if r.testBit i then acc ||| (1 <<< r) else acc) 0
def ttWires (n : Nat) (gs : Circuit) : List Nat :=
  let full := 2^(2^n) - 1
  gs.foldl (fun w g =>
    let a := w.getD g.a 0; let b := w.getD g.b 0
    w ++ [match g.op with | .and => a &&& b | .or => a ||| b | .not => full ^^^ a | .xor => a ^^^ b])
    ((List.range n).map (varTT n))
def tt (n : Nat) (gs : Circuit) : Nat := (ttWires n gs).getLast?.getD 0

def bits (n r : Nat) : List Bool := (List.range n).map r.testBit
/-- spec truth table from pointwise semantics -/
def ttSpec (n : Nat) (f : List Bool → Bool) : Nat :=
  (List.range (2^n)).foldl (fun acc r => if f (bits n r) then acc ||| (1 <<< r) else acc) 0
end LE
