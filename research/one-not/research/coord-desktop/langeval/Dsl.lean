import Proto1lib
import Batteries.Data.UnionFind
import Std.Data.HashMap
namespace LE
/-! Python-flavoured surface syntax as a Lean macro: elaborates to the SAME `Circuit` term. -/
declare_syntax_cat gate
syntax ident " = " ident " & " ident : gate
syntax ident " = " ident " | " ident : gate
syntax ident " = " ident " ^ " ident : gate
syntax ident " = " "~" ident : gate
open Lean Elab Term Meta in
elab "circuit" "(" ins:ident,* ")" ":" gs:(colGe gate)* : term => do
  let mut env : Std.HashMap Name Nat := {}
  for i in ins.getElems do env := env.insert i.getId env.size
  let mut out : Array (TSyntax `term) := #[]
  for g in gs do
    let look (x : TSyntax `ident) : TermElabM (TSyntax `term) :=
      match env[x.getId]? with
      | some k => pure (Syntax.mkNumLit (toString k))
      | none => throwErrorAt x "unknown wire {x.getId}"
    let (o, t) ← match g with
      | `(gate| $o:ident = $a:ident & $b:ident) => do pure (o, ← `(Gate.mk .and $(← look a) $(← look b)))
      | `(gate| $o:ident = $a:ident | $b:ident) => do pure (o, ← `(Gate.mk .or $(← look a) $(← look b)))
      | `(gate| $o:ident = $a:ident ^ $b:ident) => do pure (o, ← `(Gate.mk .xor $(← look a) $(← look b)))
      | `(gate| $o:ident = ~ $a:ident) => do pure (o, ← `(Gate.mk .not $(← look a) 0))
      | _ => throwUnsupportedSyntax
    env := env.insert o.getId env.size; out := out.push t
  elabTerm (← `(([$out,*] : Circuit))) none

def maj3' : Circuit := circuit (x, y, z):
  a = x & y
  b = x | y
  c = z & b
  out = a | c
#eval maj3'
theorem maj3'_tt : tt 3 maj3' = 232 := by decide
-- Python-style imperative code in `do` notation; verified union-find from Batteries
def components (n : Nat) (edges : List (Nat × Nat)) : Nat := Id.run do
  let mut uf := Batteries.UnionFind.empty
  for _ in [0:n] do uf := uf.push
  let mut comps := n
  for (a, b) in edges do
    let (uf1, same) := uf.checkEquiv! a b
    if !same then comps := comps - 1
    uf := uf1.union! a b
  return comps
#eval components 6 [(0,1),(1,2),(3,4)]
end LE
