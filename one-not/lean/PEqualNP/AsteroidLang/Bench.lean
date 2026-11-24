import PEqualNP.W951.SearchCheck
/-!
# The `.bench` netlist format: reader and writer

asteroid keeps every circuit in one file format, the ISCAS `.bench` netlist format. The grammar that
this module implements is written out in `asteroid/BENCH.md`; that page is the specification and this
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
* `parse : String → Except String Netlist`: the reader. Purely syntactic: any operator name is read.
* `print : Netlist → String`: the writer, in one canonical layout.
* `toCirc : Netlist → Except String SearchCheck.Circ`: the meaning of a file. Inputs are numbered in
  order of appearance, gates are put in topological order, only `AND`, `OR`, `NOT` (and `BUFF`, which
  is an alias and costs no gate) are accepted.
* `ofCirc : SearchCheck.Circ → Netlist`: the file for a circuit (inputs `x0, x1, …`, gates `g0, g1, …`).
* `read : String → Except String SearchCheck.Circ`: `parse` then `toCirc`, with line numbers in errors.

Everything works on `List Char`, so the module needs nothing beyond Lean core and `SearchCheck`.
Nothing is proved in this file; `BenchTest.lean` holds the tests.
-/

namespace AsteroidLang.Bench

open SearchCheck (Gate Circ)

/-- A `.bench` file as written. `gates` holds one entry per assignment line, in file order:
signal name, operator (upper case), operand names. `ors` holds the `#@ or` directives, in file order:
output name and the inputs whose OR that output must compute. `name` is the text of the first line
when that line is an ordinary comment, and `""` otherwise. -/
structure Netlist where
  name : String := ""
  inputs : List String := []
  outputs : List String := []
  gates : List (String × String × List String) := []
  ors : List (String × List String) := []
  deriving Repr, DecidableEq, Inhabited

/-! ## Characters and tokens -/

/-- Characters allowed in a signal name: letters, digits, `_`, `.`, `[`, `]`. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '[' || c == ']'

def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

def isIdent (s : String) : Bool := !s.isEmpty && s.toList.all isIdentChar

def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile isBlank).reverse.dropWhile isBlank).reverse

/-- Split at every `'\n'`. A final newline does not start another line. -/
def splitLines (cs : List Char) : List (List Char) :=
  let (cur, acc) := cs.foldl
    (fun (st : List Char × List (List Char)) c =>
      if c == '\n' then ([], st.1.reverse :: st.2) else (c :: st.1, st.2)) ([], [])
  (if cur.isEmpty then acc else cur.reverse :: acc).reverse

/-- Tokens of a statement: identifiers and the four punctuation marks `( ) , =`. -/
def tokenize (cs : List Char) : Except String (List String) :=
  let flush (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc else String.ofList cur.reverse :: acc
  let rec go (cs : List Char) (cur : List Char) (acc : List String) : Except String (List String) :=
    match cs with
    | [] => .ok (flush cur acc).reverse
    | c :: rest =>
      if isIdentChar c then go rest (c :: cur) acc
      else if isBlank c then go rest [] (flush cur acc)
      else if c == '(' || c == ')' || c == ',' || c == '=' then
        go rest [] (String.singleton c :: flush cur acc)
      else .error s!"unexpected character '{c}'"
  go cs [] []

/-- `a , b , c )` to `[a, b, c]`. -/
def parseArgs : List String → Except String (List String)
  | [x, ")"] => if isIdent x then .ok [x] else .error "expected a signal name before ')'"
  | x :: "," :: rest =>
    if isIdent x then (parseArgs rest).map (x :: ·) else .error "expected a signal name before ','"
  | _ => .error "expected operands 'NAME, NAME, ...' and a closing ')'"

/-- One line of a file. -/
inductive Stmt where
  | blank
  | comment (text : String)
  | input (x : String)
  | output (x : String)
  | gate (x op : String) (args : List String)
  | orDir (out : String) (ins : List String)
  deriving Repr, DecidableEq

/-- Words of a directive body: split at blanks, with `=` a word of its own. -/
def dirWords (cs : List Char) : List String :=
  let flush (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc else String.ofList cur.reverse :: acc
  let (cur, acc) := cs.foldl
    (fun (st : List Char × List String) c =>
      if isBlank c then ([], flush st.1 st.2)
      else if c == '=' then ([], "=" :: flush st.1 st.2)
      else (c :: st.1, st.2)) ([], [])
  (flush cur acc).reverse

/-- Read one line (without its line number). -/
def parseLine (line : List Char) : Except String Stmt :=
  let t := trimChars line
  match t with
  | '#' :: '@' :: body =>
    match dirWords body with
    | "or" :: out :: "=" :: ins =>
      if !isIdent out then .error s!"directive '#@ or': '{out}' is not a signal name"
      else if ins.isEmpty then .error "directive '#@ or': no inputs after '='"
      else match ins.find? (fun x => !isIdent x) with
        | some x => .error s!"directive '#@ or': '{x}' is not a signal name"
        | none => .ok (.orDir out ins)
    | "or" :: _ => .error "directive '#@ or': expected '#@ or OUTPUT = INPUT INPUT ...'"
    | w :: _ => .error s!"unknown directive '#@ {w}' (the only directive is '#@ or')"
    | [] => .error "empty directive '#@'"
  | '#' :: body => .ok (.comment (String.ofList (trimChars body)))
  | _ =>
    let code := trimChars (t.takeWhile (· != '#'))
    if code.isEmpty then .ok .blank else
    match tokenize code with
    | .error e => .error e
    | .ok toks =>
      match toks with
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

/-! ## Reader -/

/-- Read a `.bench` file. Errors name the line. -/
def parse (src : String) : Except String Netlist :=
  let lines := splitLines src.toList
  let rec go (ls : List (List Char)) (ln : Nat) (acc : Netlist) : Except String Netlist :=
    match ls with
    | [] => .ok { acc with inputs := acc.inputs.reverse, outputs := acc.outputs.reverse,
                           gates := acc.gates.reverse, ors := acc.ors.reverse }
    | l :: rest =>
      match parseLine l with
      | .error e => .error s!"line {ln}: {e}"
      | .ok s =>
        go rest (ln + 1) (match s with
          | .blank => acc
          | .comment t => if ln == 1 then { acc with name := t } else acc
          | .input x => { acc with inputs := x :: acc.inputs }
          | .output x => { acc with outputs := x :: acc.outputs }
          | .gate x op args => { acc with gates := (x, op, args) :: acc.gates }
          | .orDir o ins => { acc with ors := (o, ins) :: acc.ors })
  go lines 1 {}

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
  signal : Option String
  msg : String

def lookup (env : List (String × Nat)) (x : String) : Option Nat :=
  (env.find? (·.1 == x)).map (·.2)

def firstDup : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDup xs

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
def pass (n : Nat) : List (String × String × List String) → List (String × Nat) → Array Gate →
    List (String × String × List String) →
    List (String × Nat) × Array Gate × List (String × String × List String)
  | [], env, gs, later => (env, gs, later.reverse)
  | g :: rest, env, gs, later =>
    match g.2.2.mapM (lookup env) with
    | none => pass n rest env gs (g :: later)
    | some ws =>
      let a := ws.getD 0 0
      if g.2.1 == "BUFF" then pass n rest ((g.1, a) :: env) gs later
      else
        let gate : Gate :=
          if g.2.1 == "AND" then ⟨0, a, ws.getD 1 0⟩
          else if g.2.1 == "OR" then ⟨1, a, ws.getD 1 0⟩
          else ⟨2, a, a⟩
        pass n rest ((g.1, n + gs.size) :: env) (gs.push gate) later

/-- Repeat `pass` until every gate is placed or a pass places none (then there is a cycle). -/
def place (n : Nat) : Nat → List (String × String × List String) → List (String × Nat) → Array Gate →
    Except CircError (List (String × Nat) × Array Gate)
  | _, [], env, gs => .ok (env, gs)
  | 0, g :: _, _, _ => .error ⟨some g.1, s!"{showGate g}: this gate is on a cycle"⟩
  | fuel + 1, todo@(g :: _), env, gs =>
    let (env', gs', later) := pass n todo env gs []
    if later.length == todo.length then .error ⟨some g.1, s!"{showGate g}: this gate is on a cycle"⟩
    else place n fuel later env' gs'

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
  let inputEnv := nl.inputs.zipIdx
  let (env, gs) ← place n nl.gates.length nl.gates inputEnv #[]
  let wire (x : String) : Except CircError Nat :=
    match lookup env x with
    | some w => pure w
    | none => throw ⟨none, s!"output {x} is never defined"⟩
  let outWires ← nl.outputs.mapM wire
  if nl.ors.isEmpty then
    return ⟨n, [], outWires, gs.toList⟩
  if let some x := nl.outputs.find? (fun x => !(nl.ors.map (·.1)).contains x) then
    throw ⟨none, s!"output {x} has no '#@ or' directive (either every output has one, or none has)"⟩
  let mut sets : List (List Nat) := []
  let mut outs : List Nat := []
  for (o, ins) in nl.ors do
    if !nl.outputs.contains o then
      throw ⟨none, s!"directive '#@ or {o} = ...': {o} is not declared with OUTPUT({o})"⟩
    let s ← ins.mapM (fun x => match lookup inputEnv x with
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
      let lines := (splitLines src.toList).zipIdx
      let hit := e.signal.bind fun s => lines.find? fun (l, _) =>
        match parseLine l with
        | .ok (.gate x _ _) => x == s
        | _ => false
      match hit with
      | some (_, i) => .error s!"line {i + 1}: {e.msg}"
      | none => .error e.msg

/-! ## From a circuit to a netlist -/

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

end AsteroidLang.Bench
