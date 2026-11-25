import AsteroidLang.Program
/-!
# asteroid: the evaluator

`Expr.eval` is the verdict of a claim and `run` the verdicts of a program. They are the functions
the executable calls, and the functions `AsteroidLang/Semantics.lean` proves sound: a claim
evaluated to `true` holds in the project's own definitions. The checkers behind them are those of
`AsteroidLang/Core.lean`.
-/
namespace AsteroidLang
open Core

/-- the circuits defined so far, by name -/
abbrev Env := Std.HashMap String Circ

/-- the circuit of a name, if it is defined and each of its sets is a list of distinct inputs -/
def Env.circ? (env : Env) (name : String) : Option Circ :=
  match env[name]? with
  | some C => if C.setsOk then some C else none
  | none => none

/-- the value of a count on a circuit -/
def Func.eval (f : Func) (C : Circ) : Int :=
  match f with
  | .gates => C.gates.length
  | .nots => C.nots
  | .base => C.base 0
  | .witness => C.witness
  | .orwitness => C.orWitness 0
  | .slack => (C.orWitness 0 : Int) - (C.base 0 : Int)
  | .anyslack => (C.witness : Int) - (C.base 0 : Int)

/-- the value of one side of a comparison -/
def Term.eval (env : Env) : Term → Option Int
  | .int k => some k
  | .app f name => (env.circ? name).map f.eval

/-- the comparison of two integers -/
def Op.holds (op : Op) (x y : Int) : Bool :=
  match op with
  | .eq => decide (x = y)
  | .ne => decide (x ≠ y)
  | .lt => decide (x < y)
  | .le => decide (x ≤ y)
  | .gt => decide (x > y)
  | .ge => decide (x ≥ y)

/-- **The verdict of a claim.** `none`: a circuit it names is not defined or not well formed. -/
def Expr.eval (env : Env) : Expr → Option Bool
  | .correct name =>
    (env.circ? name).map fun C => C.correct && decide (C.sets.length ≤ C.outs.length)
  | .hyps name want => (env.circ? name).map fun C => C.hyps == want
  | .forallCubes name => (env.circ? name).map Circ.slackNonneg
  | .cmp l op r => do
    let x ← l.eval env
    let y ← r.eval env
    pure (op.holds x y)
  | .not e => (e.eval env).map (!·)

/-- what a program does, once its files are read: it defines circuits and makes claims -/
inductive Item
  /-- a circuit gets a name -/
  | circuit (name : String) (C : Circ)
  /-- a claim, with the line it is on -/
  | claim (line : Nat) (e : Expr)

/-- a claim, the circuits in scope where it was made, and its verdict -/
structure Verdict where
  /-- the line of the claim -/
  line : Nat
  /-- the circuits defined before it -/
  env : Env
  /-- the claim -/
  claim : Expr
  /-- its verdict -/
  value : Bool

/-- **The verdicts of a program**, in order; an error if a claim has no verdict. -/
def run (env : Env) : List Item → Except String (List Verdict)
  | [] => .ok []
  | .circuit name C :: rest => run (env.insert name C) rest
  | .claim line e :: rest =>
    match e.eval env with
    | none => .error s!"line {line}: no verdict: a circuit named in this claim is not defined, \
        or one of its sets repeats a point or names a point that is not an input"
    | some b => (run env rest).map (⟨line, env, e, b⟩ :: ·)

/-- a truth value as the reference implementation prints it -/
def showBool (b : Bool) : String := if b then "True" else "False"

/-- the words printed after a verdict: the numbers behind it -/
def Expr.detail (env : Env) : Expr → String
  | .correct name =>
    s!"correct = {showBool ((Expr.correct name).eval env == some true)}"
  | .hyps name _ => s!"hyps = {showBool ((env.circ? name).any Circ.hyps)}"
  | .forallCubes name =>
    match env.circ? name with
    | some C =>
      let table := C.slackTable
      let worst := table.foldl min (table.headD 0)
      let alive := ((List.range (2 ^ C.n)).filter fun q => 0 < C.base q).length
      s!"least slack over {2 ^ C.n} cubes = {worst} ({alive} cubes with positive base)"
    | none => ""
  | .cmp l op r => s!"{(l.eval env).getD 0} {op.text} {(r.eval env).getD 0}"
  | .not e => "not: " ++ e.detail env

end AsteroidLang
