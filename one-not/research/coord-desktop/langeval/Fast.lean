import Proto1lib
namespace LE
def opOf : Nat → Op | 0 => .and | 1 => .or | 2 => .not | _ => .xor
/-- closed form: truth table of x_i on 2^n rows = ((2^(2^n)-1) / (2^(2^i)+1)) <<< 2^i; all GMP ops in the kernel -/
def varTT' (n i : Nat) : Nat := ((2^(2^n) - 1) / (2^(2^i) + 1)) <<< (2^i)
/-- packed evaluator: wires kept in a list, newest first; 16 bits/gate (op:2,a:7,b:7) -/
def ttGo (full : Nat) : Nat → Nat → List Nat → Nat → List Nat
  | 0, _, w, _ => w
  | g+1, c, w, len =>
    let x := c &&& 0xFFFF
    let a := w.getD (len - 1 - ((x >>> 7) &&& 127)) 0
    let b := w.getD (len - 1 - (x &&& 127)) 0
    let v := match x >>> 14 with | 0 => a &&& b | 1 => a ||| b | 2 => full ^^^ a | _ => a ^^^ b
    ttGo full g (c >>> 16) (v :: w) (len+1)
def ttP (n g c : Nat) : Nat :=
  (ttGo (2^(2^n)-1) g c ((List.range n).reverse.map (varTT' n)) n).headD 0
def checkAll' (n g : Nat) (cs : List (Nat × Nat)) : Bool := cs.all fun p => ttP n g p.1 == p.2
theorem varTT'_ok : (List.range 5).all (fun i => varTT' 5 i == varTT 5 i) = true := by decide +kernel
end LE
