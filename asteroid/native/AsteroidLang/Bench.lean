import Std.Data.HashMap
import AsteroidLang.Core
/-!
# The `.bench` netlist format: reader and writer

asteroid keeps every circuit in one file format, the ISCAS `.bench` netlist format. The grammar that
this module implements is written out in `asteroid/BENCH.md`; that page is the specification and
this
file follows it line by line.

```
# two sets sharing the point x2
INPUT(x0)
INPUT(x1)
INPUT(x2)
INPUT(x3)
OUTPUT(b)
OUTPUT(c)
#@ or b = x0 x1 x2
#@ or c = x2 x3
a = OR(x0, x1)
b = OR(a, x2)
c = OR(x2, x3)
```

## What is here

* `Netlist`: a file as written (names, not wire numbers), in file order.
* `parse : String → Except String Netlist`: the reader. Purely syntactic: any operator name is
  read.
* `print : Netlist → String`: the writer, in one canonical layout.
* `toCirc : Netlist → Except String Core.Circ`: the meaning of a file. Inputs are numbered in
  order of appearance, gates are put in topological order, only `AND`, `OR`, `NOT` (and `BUFF`,
  which
  is an alias and costs no gate) are accepted.
* `ofCirc : Core.Circ → Netlist`: the file for a circuit (inputs `x0, x1, …`, gates `g0,
  g1, …`).
* `read : String → Except String Core.Circ`: `parse` then `toCirc`, with line numbers in
  errors.

* `toAag : Core.Circ → String`: export to ASCII AIGER (`research/notes/aiger.md`); the function is
  kept, the gate count and the NOT count are not.

The reader uses only the public standard library: `String.splitOn`, `String.trimAscii`,
`String.replace`, `String.splitToList`, `List`, `Array`, `Except` and `Std.HashMap`. Nothing is
proved
in this file; `BenchTest.lean` holds the tests.
-/

namespace AsteroidLang.Bench

open AsteroidLang.Core (Gate Circ)

/-- A `.bench` file as written. `gates` holds one entry per assignment line, in file order:
signal name, operator (upper case), operand names. `ors` holds the `#@ or` directives, in file
order:
output name and the inputs whose OR that output must compute. `name` is the text of the first line
when that line is an ordinary comment, and `""` otherwise. -/
structure Netlist where
  name : String := ""
  inputs : List String := []
  outputs : List String := []
  gates : List (String × String × List String) := []
  ors : List (String × List String) := []
  deriving Repr, DecidableEq, Inhabited

/-- An assignment line: signal name, operator, operand names. -/
abbrev GateLine := String × String × List String

/-! ## Lines and tokens -/

/-- Characters allowed in a signal name: letters, digits, `_`, `.`, `[`, `]`. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '[' || c == ']'

/-- A signal name: one or more identifier characters. -/
def isIdent (s : String) : Bool := !s.isEmpty && s.all isIdentChar

/-- The four punctuation marks of a statement. -/
def punctuation : List String := ["(", ")", ",", "="]

/-- The blank-separated words of a string, with each mark in `marks` a word of its own. -/
def words (marks : List String) (s : String) : List String :=
  ((marks.foldl (fun t m => t.replace m (" " ++ m ++ " ")) s).splitToList Char.isWhitespace).filter
    (!·.isEmpty)

/-- Tokens of a statement: signal names and punctuation. Any other character is an error. -/
def tokenize (s : String) : Except String (List String) :=
  let toks := words punctuation s
  match toks.find? (fun t => !(punctuation.contains t || isIdent t)) with
  | some t => .error s!"unexpected character in '{t}'"
  | none => .ok toks

/-- `a , b , c )` to `[a, b, c]`. -/
def parseArgs : List String → Except String (List String)
  | [x, ")"] => if isIdent x then .ok [x] else .error "expected a signal name before ')'"
  | x :: "," :: rest =>
    if isIdent x then (parseArgs rest).map (x :: ·) else .error "expected a signal name before ','"
  | _ => .error "expected operands 'NAME, NAME, ...' and a closing ')'"

/-- One line of a file. -/
inductive Stmt where
  /-- An empty line. -/
  | blank
  /-- An ordinary comment `# text`. -/
  | comment (text : String)
  /-- `INPUT(x)`. -/
  | input (x : String)
  /-- `OUTPUT(x)`. -/
  | output (x : String)
  /-- `x = OP(args)`, with `op` in upper case. -/
  | gate (x op : String) (args : List String)
  /-- `#@ or out = ins`. -/
  | orDir (out : String) (ins : List String)
  deriving Repr, DecidableEq

/-- Read a directive body (the text after `#@`). -/
def parseDirective (body : String) : Except String Stmt :=
  match words ["="] body with
  | "or" :: out :: "=" :: ins =>
    if !isIdent out then .error s!"directive '#@ or': '{out}' is not a signal name"
    else if ins.isEmpty then .error "directive '#@ or': no inputs after '='"
    else match ins.find? (fun x => !isIdent x) with
      | some x => .error s!"directive '#@ or': '{x}' is not a signal name"
      | none => .ok (.orDir out ins)
  | "or" :: _ => .error "directive '#@ or': expected '#@ or OUTPUT = INPUT INPUT ...'"
  | w :: _ => .error s!"unknown directive '#@ {w}' (the only directive is '#@ or')"
  | [] => .error "empty directive '#@'"

/-- Read a statement (a line with its comment removed, not empty). -/
def parseStatement (code : String) : Except String Stmt := do
  match ← tokenize code with
  | [kw, "(", x, ")"] =>
    if !isIdent x then .error "expected a signal name between '(' and ')'"
    else if kw.toUpper == "INPUT" then .ok (.input x)
    else if kw.toUpper == "OUTPUT" then .ok (.output x)
    else .error s!"expected INPUT(NAME), OUTPUT(NAME) or NAME = OP(...), found '{kw}(...)'"
  | x :: "=" :: op :: "(" :: rest =>
    if !isIdent x then .error "expected a signal name before '='"
    else if !isIdent op then .error "expected an operator name after '='"
    else (parseArgs rest).map (fun args => .gate x op.toUpper args)
  | _ => .error "expected INPUT(NAME), OUTPUT(NAME) or NAME = OP(NAME, ...)"

/-- Read one line (without its line number). -/
def parseLine (line : String) : Except String Stmt :=
  let t := line.trimAscii.toString
  if t.startsWith "#@" then parseDirective (t.drop 2).toString
  else if t.startsWith "#" then .ok (.comment (t.drop 1).trimAscii.toString)
  else
    let code := ((t.splitOn "#").headD "").trimAscii.toString
    if code.isEmpty then .ok .blank else parseStatement code

/-! ## Reader -/

/-- Read a `.bench` file. Errors name the line. -/
def parse (src : String) : Except String Netlist := do
  let mut acc : Netlist := {}
  for (l, i) in (src.splitOn "\n").zipIdx do
    match parseLine l with
    | .error e => throw s!"line {i + 1}: {e}"
    | .ok .blank => pure ()
    | .ok (.comment t) => if i == 0 then acc := { acc with name := t }
    | .ok (.input x) => acc := { acc with inputs := x :: acc.inputs }
    | .ok (.output x) => acc := { acc with outputs := x :: acc.outputs }
    | .ok (.gate x op args) => acc := { acc with gates := (x, op, args) :: acc.gates }
    | .ok (.orDir o ins) => acc := { acc with ors := (o, ins) :: acc.ors }
  return { acc with inputs := acc.inputs.reverse, outputs := acc.outputs.reverse,
                    gates := acc.gates.reverse, ors := acc.ors.reverse }

/-! ## Writer -/

/-- Write a netlist: the name as a comment, the inputs, the outputs, the directives, the gates. -/
def print (n : Netlist) : String :=
  let ls : List String :=
    (if n.name.isEmpty then [] else ["# " ++ n.name]) ++
    n.inputs.map (fun x => "INPUT(" ++ x ++ ")") ++
    n.outputs.map (fun x => "OUTPUT(" ++ x ++ ")") ++
    n.ors.map (fun (o, ins) => "#@ or " ++ o ++ " = " ++ " ".intercalate ins) ++
    n.gates.map (fun (x, op, args) => x ++ " = " ++ op ++ "(" ++ ", ".intercalate args ++ ")")
  String.join (ls.map (· ++ "\n"))

/-! ## From a netlist to a circuit -/

/-- An error of `toCirc`: the signal whose defining line is at fault, when there is one. -/
structure CircError where
  /-- The signal whose assignment line is at fault. -/
  signal : Option String
  /-- The message, without a line number. -/
  msg : String

/-- The wire of each signal placed so far. -/
abbrev Env := Std.HashMap String Nat

/-- The first element that occurs again later in the list. -/
def firstDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDup xs

/-- An assignment line as `print` writes it. -/
def showGate (g : String × String × List String) : String :=
  g.1 ++ " = " ++ g.2.1 ++ "(" ++ ", ".intercalate g.2.2 ++ ")"

/-- The operators asteroid accepts, with their number of operands. -/
def checkOp (g : String × String × List String) : Except CircError Unit :=
  let (x, op, args) := g
  let bad (m : String) : Except CircError Unit := .error ⟨some x, s!"{showGate g}: {m}"⟩
  if op == "AND" || op == "OR" then
    if args.length == 2 then .ok () else bad s!"{op} takes exactly 2 operands, found {args.length}"
  else if op == "NOT" || op == "BUFF" then
    if args.length == 1 then .ok () else bad s!"{op} takes exactly 1 operand, found {args.length}"
  else bad s!"operator {op} is not accepted (asteroid accepts AND, OR, NOT and BUFF)"

/-- One pass over the gates not yet placed. A gate whose operands all have wires is placed at once,
so a file already in topological order is finished in one pass and keeps its order. -/
def pass (n : Nat) : List GateLine → Env → Array Gate →
    List GateLine →
    Env × Array Gate × List GateLine
  | [], env, gs, later => (env, gs, later.reverse)
  | g :: rest, env, gs, later =>
    match g.2.2.mapM (env[·]?) with
    | none => pass n rest env gs (g :: later)
    | some ws =>
      let a := ws.getD 0 0
      if g.2.1 == "BUFF" then pass n rest (env.insert g.1 a) gs later
      else
        let gate : Gate :=
          if g.2.1 == "AND" then ⟨0, a, ws.getD 1 0⟩
          else if g.2.1 == "OR" then ⟨1, a, ws.getD 1 0⟩
          else ⟨2, a, a⟩
        pass n rest (env.insert g.1 (n + gs.size)) (gs.push gate) later

/-- Repeat `pass` until every gate is placed or a pass places none (then there is a cycle). -/
def place (n : Nat) : Nat → List GateLine → Env → Array Gate →
    Except CircError (Env × Array Gate)
  | _, [], env, gs => .ok (env, gs)
  | 0, g :: _, _, _ => .error ⟨some g.1, s!"{showGate g}: this gate is on a cycle"⟩
  | fuel + 1, todo@(g :: _), env, gs =>
    let (env', gs', later) := pass n todo env gs []
    if later.length == todo.length then
      .error ⟨some g.1, s!"{showGate g}: this gate is on a cycle"⟩
    else place n fuel later env' gs'

/-- `toCirc` with a structured error. -/
def toCircCore (nl : Netlist) : Except CircError Circ := do
  let n := nl.inputs.length
  if let some x := firstDup nl.inputs then throw ⟨none, s!"input {x} is declared twice"⟩
  if let some x := firstDup nl.outputs then throw ⟨none, s!"output {x} is declared twice"⟩
  let defined := nl.gates.map (·.1)
  if let some x := firstDup defined then throw ⟨some x, s!"signal {x} is assigned twice"⟩
  if let some x := defined.find? nl.inputs.contains then
    throw ⟨some x, s!"signal {x} is an input and is also assigned"⟩
  nl.gates.forM checkOp
  for g in nl.gates do
    if let some a := g.2.2.find? (fun a => !(nl.inputs.contains a || defined.contains a)) then
      throw ⟨some g.1, s!"{showGate g}: signal {a} is never defined"⟩
  let inputEnv : Env := Std.HashMap.ofList nl.inputs.zipIdx
  let (env, gs) ← place n nl.gates.length nl.gates inputEnv #[]
  let wire (x : String) : Except CircError Nat :=
    match env[x]? with
    | some w => pure w
    | none => throw ⟨none, s!"output {x} is never defined"⟩
  let outWires ← nl.outputs.mapM wire
  if nl.ors.isEmpty then
    return ⟨n, [], outWires, gs.toList⟩
  if let some x := nl.outputs.find? (fun x => !(nl.ors.map (·.1)).contains x) then
    throw ⟨none, s!"output {x} has no '#@ or' directive (every output needs one, or none)"⟩
  let mut sets : List (List Nat) := []
  let mut outs : List Nat := []
  for (o, ins) in nl.ors do
    if !nl.outputs.contains o then
      throw ⟨none, s!"directive '#@ or {o} = ...': {o} is not declared with OUTPUT({o})"⟩
    let s ← ins.mapM (fun x => match inputEnv[x]? with
      | some i => pure i
      | none => throw (CircError.mk none s!"directive '#@ or {o} = ...': {x} is not an input"))
    sets := s :: sets
    outs := (← wire o) :: outs
  return ⟨n, sets.reverse, outs.reverse, gs.toList⟩

/-- The circuit a netlist denotes. Inputs are numbered in order of appearance; wire `i < n` is input
`i` and wire `n + k` is gate `k`. Every `AND`, `OR`, `NOT` line is one gate; a `BUFF` line is none.
With no directive the circuit has no sets and `outs` lists the outputs in order; with directives,
`sets` and `outs` follow the directives in order. -/
def toCirc (nl : Netlist) : Except String Circ :=
  match toCircCore nl with
  | .ok C => .ok C
  | .error e => .error e.msg

/-- `parse` then `toCirc`. An error about a gate names the line of the file that defines it. -/
def read (src : String) : Except String Circ :=
  match parse src with
  | .error e => .error e
  | .ok nl =>
    match toCircCore nl with
    | .ok C => .ok C
    | .error e =>
      let lines := (src.splitOn "\n").zipIdx
      let hit := e.signal.bind fun s => lines.find? fun (l, _) =>
        match parseLine l with
        | .ok (.gate x _ _) => x == s
        | _ => false
      match hit with
      | some (_, i) => .error s!"line {i + 1}: {e.msg}"
      | none => .error e.msg

/-! ## From a circuit to a netlist -/

/-- The name `ofCirc` gives to wire `w` of a circuit with `n` inputs. -/
def wireName (n w : Nat) : String := if w < n then s!"x{w}" else s!"g{w - n}"

/-- The netlist of a circuit: inputs `x0 … x(n-1)`, gate `k` named `gk`, one `#@ or` directive per
set. Op code 0 is `AND`, 1 is `OR`, anything else is `NOT` of the first wire. -/
def ofCirc (C : Circ) (name : String := "") : Netlist :=
  let w := wireName C.n
  { name := name
    inputs := (List.range C.n).map w
    outputs := (C.outs.map w).eraseDups
    gates := C.gates.zipIdx.map fun (g, k) =>
      (w (C.n + k),
        if g.op == 0 then ("AND", [w g.a, w g.b])
        else if g.op == 1 then ("OR", [w g.a, w g.b])
        else ("NOT", [w g.a]))
    ors := (C.sets.zip C.outs).map fun (S, o) => (w o, S.map w) }

/-! ## Export to AIGER -/

/-- The circuit as an ASCII AIGER file (`aag M I L O A`, no latches). Input `i` is variable `i + 1`.
An `AND` gate is one AIGER and; an `OR` gate is one AIGER and with its two inputs and its output
negated; a `NOT` gate is no AIGER and, only the negated literal of its operand. The outputs are
`C.outs` in order. The function computed at every output is kept; the number of gates and the number
of NOT gates are not. -/
def toAag (C : Circ) : String :=
  let neg (l : Nat) : Nat := if l % 2 == 0 then l + 1 else l - 1
  let (lits, ands) := C.gates.foldl
    (fun (st : Array Nat × Array String) g =>
      let (lits, ands) := st
      let a := lits.getD g.a 0
      let b := lits.getD g.b 0
      let v := 2 * (C.n + ands.size + 1)
      let line (x y : Nat) : String := s!"{v} {max x y} {min x y}"
      if g.op == 0 then (lits.push v, ands.push (line a b))
      else if g.op == 1 then (lits.push (v + 1), ands.push (line (neg a) (neg b)))
      else (lits.push (neg a), ands))
    (((List.range C.n).map (fun i => 2 * (i + 1))).toArray, #[])
  let header := s!"aag {C.n + ands.size} {C.n} 0 {C.outs.length} {ands.size}"
  let ls := header :: (List.range C.n).map (fun i => toString (2 * (i + 1))) ++
    C.outs.map (fun o => toString (lits.getD o 0)) ++ ands.toList
  String.join (ls.map (· ++ "\n"))

end AsteroidLang.Bench
