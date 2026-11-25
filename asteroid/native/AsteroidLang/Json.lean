/-!
# A small JSON reader for the asteroid executable

`Lean.Data.Json` links the whole Lean compiler (Meta, Elab) into the executable, about 80 MB. The
circuit files need only objects, arrays, strings, whole numbers, `true`, `false` and `null`, so this
reader handles exactly those; a number with a fraction or exponent is kept as its text (`real`). It imports nothing.
-/

namespace AsteroidLang.Json

/-- a JSON value -/
inductive Val where
  | null
  | bool (b : Bool)
  | num (i : Int)
  | real (text : String)
  | str (s : String)
  | arr (xs : List Val)
  | obj (kvs : List (String × Val))
  deriving Inhabited

abbrev P := StateT (List Char) (Except String)

def ws : P Unit := modify fun cs => cs.dropWhile fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

def peek : P (Option Char) := do ws; return (← get).head?

def expect (c : Char) : P Unit := do
  ws
  match ← get with
  | d :: rest => if c == d then set rest else throw s!"expected '{c}', found '{d}'"
  | [] => throw s!"expected '{c}', found the end"

def lit (w : String) (v : Val) : P Val := do
  let cs ← get
  if cs.take w.length == w.toList then set (cs.drop w.length); return v
  else throw s!"bad literal near '{String.ofList (cs.take 10)}'"

partial def strBody (acc : List Char) : P String := do
  match ← get with
  | '"' :: rest => set rest; return String.ofList acc.reverse
  | '\\' :: c :: rest =>
    set rest
    let d := match c with | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | c => c
    strBody (d :: acc)
  | c :: rest => set rest; strBody (c :: acc)
  | [] => throw "unterminated string"

def number : P Val := do
  let cs ← get
  let (neg, cs) := match cs with | '-' :: r => (true, r) | r => (false, r)
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then throw "bad number"
  let rest := cs.drop ds.length
  let numChar (c : Char) := c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'
  if let c :: _ := rest then
    if c == '.' || c == 'e' || c == 'E' then
      let tail := rest.takeWhile numChar
      set (rest.drop tail.length)
      return .real (String.ofList ((if neg then ['-'] else []) ++ ds ++ tail))
  set rest
  let n : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0
  return .num (if neg then -(n : Int) else n)

mutual
partial def value : P Val := do
  match ← peek with
  | some '{' => expect '{'; obj []
  | some '[' => expect '['; arr []
  | some '"' => expect '"'; return .str (← strBody [])
  | some 't' => lit "true" (.bool true)
  | some 'f' => lit "false" (.bool false)
  | some 'n' => lit "null" .null
  | some _ => number
  | none => throw "unexpected end"
partial def arr (acc : List Val) : P Val := do
  if (← peek) == some ']' then expect ']'; return .arr acc.reverse
  let v ← value
  match ← peek with
  | some ',' => expect ','; arr (v :: acc)
  | _ => expect ']'; return .arr (v :: acc).reverse
partial def obj (acc : List (String × Val)) : P Val := do
  if (← peek) == some '}' then expect '}'; return .obj acc.reverse
  expect '"'
  let k ← strBody []
  expect ':'
  let v ← value
  match ← peek with
  | some ',' => expect ','; obj ((k, v) :: acc)
  | _ => expect '}'; return .obj ((k, v) :: acc).reverse
end

/-- parse a whole document -/
def parse (src : String) : Except String Val := do
  let (v, rest) ← (do let v ← value; ws; return v).run src.toList
  if rest.isEmpty then return v else throw "trailing text after the JSON value"

def Val.field (v : Val) (k : String) : Except String Val :=
  match v with
  | .obj kvs => match kvs.lookup k with | some x => .ok x | none => .error s!"no key '{k}'"
  | _ => .error s!"not an object (looking for '{k}')"

/-- the string at key `k`, or `d` when it is missing or not a string -/
def Val.strOr (v : Val) (k d : String) : String :=
  match v.field k with
  | .ok (.str s) => s
  | _ => d

def Val.nat : Val → Except String Nat
  | .num (.ofNat n) => .ok n
  | _ => .error "expected a whole number ≥ 0"

def Val.str? : Val → Except String String
  | .str s => .ok s
  | _ => .error "expected a string"

def Val.list : Val → Except String (List Val)
  | .arr xs => .ok xs
  | _ => .error "expected an array"

def Val.nats (v : Val) : Except String (List Nat) := do (← v.list).mapM Val.nat

def Val.at (v : Val) (i : Nat) : Except String Val := do
  match (← v.list)[i]? with | some x => .ok x | none => .error s!"no element {i}"

end AsteroidLang.Json
