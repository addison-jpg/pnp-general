import Std.Data.HashMap
import AsteroidLang.Core
/-!
# asteroid: the syntax tree of a program, and its parser

A program is a text file; a line is a statement, `#` starts a comment (`asteroid/SPEC.md`). This
file covers the core of the language: circuits written in the program, `let … = load …`, `show`,
and the claim forms `correct`, `hyps`, `forall cubes slack … >= 0`, comparisons of counts, and
`not`. Every other statement is kept as `Stmt.unsupported`, so the command line can name it.
-/
namespace AsteroidLang
open Core

/-- a count of a circuit -/
inductive Func
  | gates | nots | base | witness | orwitness | slack | anyslack
  deriving DecidableEq, Repr

/-- the count named by a word of the language -/
def Func.ofString? : String → Option Func
  | "gates" => some .gates
  | "nots" => some .nots
  | "base" => some .base
  | "witness" => some .witness
  | "orwitness" => some .orwitness
  | "slack" => some .slack
  | "anyslack" => some .anyslack
  | _ => none

/-- one side of a comparison: an integer, or a count of a named circuit -/
inductive Term
  | int (k : Int)
  | app (f : Func) (name : String)
  deriving Repr

/-- a comparison -/
inductive Op
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- the comparison as written in a program -/
def Op.text : Op → String
  | .eq => "=" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- the comparison as written in a Lean statement -/
def Op.lean : Op → String
  | .eq => "=" | .ne => "≠" | .lt => "<" | .le => "≤" | .gt => ">" | .ge => "≥"

/-- a claim -/
inductive Expr
  /-- `correct(NAME)` -/
  | correct (name : String)
  /-- `hyps(NAME)`, or `hyps(NAME) = false` -/
  | hyps (name : String) (want : Bool)
  /-- `forall cubes slack(NAME) >= 0` -/
  | forallCubes (name : String)
  /-- `TERM OP TERM` -/
  | cmp (l : Term) (op : Op) (r : Term)
  /-- `not CLAIM` -/
  | not (e : Expr)
  deriving Repr

/-- a statement of a program -/
inductive Stmt
  /-- `circuit NAME N … end` -/
  | circuit (name : String) (C : Circ)
  /-- `let NAME = load PATH` -/
  | load (name path : String)
  /-- `show NAME` -/
  | display (name : String)
  /-- `claim CLAIM [by lean]`; `force` is `claim!` -/
  | claim (force : Bool) (text : String) (e : Expr) (byLean : Bool)
  /-- a statement this version does not run, with the words that name it -/
  | unsupported (what : String)

/-- a statement with its line number -/
structure Line where
  /-- the line of the program, from 1 -/
  num : Nat
  /-- the statement on it -/
  stmt : Stmt

/-- the words of a line -/
def words (s : String) : List String :=
  ((s.map fun c => if c.isWhitespace then ' ' else c).splitOn " ").filter (· ≠ "")

/-- letters, digits and `_` only -/
def isName (s : String) : Bool :=
  s ≠ "" && s.all fun c => c.isAlphanum || c == '_'

/-- names that the generated proof module could not use for a circuit -/
def reserved : List String :=
  ["tt", "varTT", "correctB", "witnessCount", "hasWitness", "Gate", "Circ", "def", "theorem",
   "end", "open", "import", "namespace", "by", "at", "in", "if", "then", "else", "let", "have",
   "show", "from", "do", "fun", "Type", "Prop", "true", "false"]

/-- `F(NAME)` as the pair `(F, NAME)` -/
def parseApp (s : String) : Option (String × String) :=
  match s.splitOn "(" with
  | [f, rest] =>
    match rest.splitOn ")" with
    | [name, ""] => if isName f && isName name then some (f, name) else none
    | _ => none
  | _ => none

/-- an integer, or a count of a circuit -/
def parseTerm (s : String) : Option Term :=
  match s.toInt? with
  | some k => some (.int k)
  | none => do
    let (f, name) ← parseApp s
    let f ← Func.ofString? f
    pure (.app f name)

/-- the comparisons, in the order they are looked for (`<=` before `<` and `=`) -/
def ops : List Op := [.le, .ge, .ne, .eq, .lt, .gt]

/-- split a claim at its comparison -/
def splitAtOp (s : String) : Option (String × Op × String) :=
  ops.findSome? fun op =>
    match s.splitOn op.text with
    | [l, r] => some (l, op, r)
    | _ => none

/-- a claim with no `not` in front, written without spaces -/
def parseFlat (s : String) : Option Expr :=
  match s.splitOn "forallcubesslack(" with
  | ["", rest] =>
    match rest.splitOn ")>=0" with
    | [name, ""] => if isName name then some (.forallCubes name) else none
    | _ => none
  | _ =>
    match splitAtOp s with
    | some (l, op, r) =>
      match parseApp l, op, r with
      | some ("hyps", name), .eq, "true" => some (.hyps name true)
      | some ("hyps", name), .eq, "false" => some (.hyps name false)
      | _, _, _ => do
        let l ← parseTerm l
        let r ← parseTerm r
        pure (.cmp l op r)
    | none =>
      match parseApp s with
      | some ("correct", name) => some (.correct name)
      | some ("hyps", name) => some (.hyps name true)
      | _ => none

/-- a claim, from its words -/
def parseExpr : List String → Option Expr
  | "not" :: ws => .not <$> parseExpr ws
  | ws => parseFlat (String.join ws)

/-- the words after `claim` or `claim!` -/
def parseClaim (force : Bool) (ws : List String) : Stmt :=
  let (byLean, body) :=
    match ws.reverse with
    | "lean" :: "by" :: body => (true, body.reverse)
    | _ => (false, ws)
  let text := " ".intercalate body
  match parseExpr body with
  | some e => .claim force text e byLean
  | none => .unsupported s!"claim {text}"

/-- a statement outside a circuit block, from its words -/
def parseStmt : List String → Stmt
  | ["let", name, "=", "load", path] => .load name path
  | ["show", name] => .display name
  | "claim" :: ws => parseClaim false ws
  | "claim!" :: ws => parseClaim true ws
  | ws => .unsupported (" ".intercalate ws)

/-- a circuit being read -/
structure Block where
  /-- its name -/
  name : String
  /-- the number of inputs -/
  n : Nat
  /-- the wire of each gate name -/
  wires : Std.HashMap String Nat := {}
  /-- the gates so far -/
  gates : Array Gate := #[]
  /-- the sets so far -/
  sets : Array (List Nat) := #[]
  /-- the output wire of each set -/
  outs : Array Nat := #[]

/-- the circuit read -/
def Block.circ (b : Block) : Circ := ⟨b.n, b.sets.toList, b.outs.toList, b.gates.toList⟩

/-- a wire: an input number, or the name of an earlier gate -/
def Block.wire? (b : Block) (w : String) : Option Nat :=
  if w.isNat then w.toNat? else b.wires[w]?

/-- add a gate under a name -/
def Block.push (b : Block) (w : String) (g : Gate) : Block :=
  { b with wires := b.wires.insert w (b.n + b.gates.size), gates := b.gates.push g }

/-- one line inside a circuit block -/
def Block.step (b : Block) (ws : List String) : Option Block :=
  match ws with
  | [w, "=", "or", x, y] => do pure (b.push w ⟨1, ← b.wire? x, ← b.wire? y⟩)
  | [w, "=", "and", x, y] => do pure (b.push w ⟨0, ← b.wire? x, ← b.wire? y⟩)
  | [w, "=", "not", x] => do
    let x ← b.wire? x
    pure (b.push w ⟨2, x, x⟩)
  | "set" :: rest =>
    match rest.reverse with
    | w :: "->" :: pts => do
      let o ← b.wire? w
      let pts ← pts.reverse.mapM fun p => if p.isNat then p.toNat? else none
      if pts.isEmpty then none else pure { b with sets := b.sets.push pts, outs := b.outs.push o }
    | _ => none
  | _ => none

/-- the path of `let NAME = load PATH`: the rest of the line after `load`, so a path may hold
spaces (`C:/Users/Some Name/x.bench`), with surrounding double or single quotes removed -/
def loadPath (line : String) : String :=
  let rest := ("=".intercalate ((line.splitOn "=").drop 1)).trimAscii.toString
  let p := (rest.drop 4).trimAscii.toString
  if p.length ≥ 2 && ((p.startsWith "\"" && p.endsWith "\"") || (p.startsWith "'" && p.endsWith "'"))
  then ((p.drop 1).dropEnd 1).toString else p

/-- refuse a circuit name the proof module could not use -/
def checkName (file : String) (ln : Nat) (name : String) : Except String Unit :=
  if reserved.contains name then
    throw s!"{file}:{ln}: the name `{name}` is taken by the proof library; pick another name \
      for this circuit"
  else if !isName name then
    throw s!"{file}:{ln}: `{name}` is not a name (letters, digits and _)"
  else pure ()

/-- read the lines from line `ln` on; `blk` is the circuit block that is open, if any -/
def parseLines (file : String) :
    Nat → Option Block → List String → Except String (List Line)
  | _, none, [] => pure []
  | _, some b, [] => throw s!"{file}: circuit {b.name} has no `end`"
  | ln, blk, raw :: rest =>
    let ws := words ((raw.splitOn "#").headD "")
    if ws.isEmpty then parseLines file (ln + 1) blk rest else
    match blk with
    | some b =>
      if ws = ["end"] then
        (⟨ln, .circuit b.name b.circ⟩ :: ·) <$> parseLines file (ln + 1) none rest
      else
        match b.step ws with
        | some b => parseLines file (ln + 1) (some b) rest
        | none => throw s!"{file}:{ln}: cannot parse inside circuit: {" ".intercalate ws}"
    | none =>
      match ws with
      | ["circuit", name, n] => do
        checkName file ln name
        match n.toNat? with
        | some n => parseLines file (ln + 1) (some { name, n }) rest
        | none => throw s!"{file}:{ln}: the number of inputs must be a number: {n}"
      | _ => do
        let stmt := match ws with
          | "let" :: name :: "=" :: "load" :: _ :: _ => .load name (loadPath ((raw.splitOn "#").headD ""))
          | _ => parseStmt ws
        if let .load name _ := stmt then checkName file ln name
        (⟨ln, stmt⟩ :: ·) <$> parseLines file (ln + 1) none rest

/-- parse a program; `file` is its name, for messages -/
def parse (file src : String) : Except String (List Line) :=
  parseLines file 1 none (src.splitOn "\n")

end AsteroidLang
