import AsteroidLang.Bench
import PEqualNP.W951.SearchCheck
/-!
# Tests of the `.bench` reader and writer

Every check here is a `#guard`: the compiled functions are run when this file is built, and the
build fails if a check is false. These are tests on the listed inputs. Nothing in this file is a
theorem.

1. `parse (print n) = n` on three netlists.
2. `toCirc` of the hello file is the `Circ` literal that asteroid generates for `hello.ath`
   (`PEqualNP/W951/Asteroid_hello.lean`).
3. `toCirc (ofCirc C) = C` on `hello` and on `SearchCheck.t4` (73 gates, 4 NOT gates).
4. Gates out of order are sorted; `BUFF` costs no gate.
5. Each kind of error, with its message.
6. The AIGER export of hello.
-/

namespace AsteroidLang.Bench.Test

open AsteroidLang.Core (Gate Circ)

/-- `SearchCheck.t4` (73 gates, 4 NOT gates) as a circuit of the reader. -/
def t4 : Circ := ⟨SearchCheck.t4.n, SearchCheck.t4.sets, SearchCheck.t4.outs,
  SearchCheck.t4.gates.map fun g => ⟨g.op, g.a, g.b⟩⟩

deriving instance DecidableEq for Gate
deriving instance DecidableEq for Circ

/-- Equality of results, for the checks below. -/
local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- The hello circuit as a file (the repository's `hello.bench`). -/
def helloSrc : String :=
"# two sets sharing the point x2
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
"

/-- The literal asteroid generates for `hello.ath`. -/
def helloCirc : Circ :=
  ⟨4, [[0, 1, 2], [2, 3]], [5, 6], [⟨1, 0, 1⟩, ⟨1, 4, 2⟩, ⟨1, 2, 3⟩]⟩

/-- A circuit with a NOT gate, gates out of order, a `BUFF`, lower-case keywords, a trailing comment
and no directive. -/
def mixedSrc : String :=
"input(a)
  INPUT ( b )

output(z)   # the only output
z = and(n, w)
w = BUFF(o)
n = NOT(a)
o = OR(a, b)"

/-- The netlist of `mixedSrc`. -/
def mixedNet : Netlist :=
  { inputs := ["a", "b"], outputs := ["z"],
    gates := [("z", "AND", ["n", "w"]), ("w", "BUFF", ["o"]), ("n", "NOT", ["a"]),
      ("o", "OR", ["a", "b"])] }

/-- Does `r` fail with a message containing `frag`? -/
def failsWith {α : Type} (r : Except String α) (frag : String) : Bool :=
  match r with
  | .error e => (e.splitOn frag).length > 1
  | .ok _ => false

/-! ### 1. Round trip `parse ∘ print` -/

#guard parse helloSrc == .ok
  { name := "two sets sharing the point x2", inputs := ["x0", "x1", "x2", "x3"],
    outputs := ["b", "c"], ors := [("b", ["x0", "x1", "x2"]), ("c", ["x2", "x3"])],
    gates := [("a", "OR", ["x0", "x1"]), ("b", "OR", ["a", "x2"]), ("c", "OR", ["x2", "x3"])] }
#guard print ((parse helloSrc).toOption.getD {}) == helloSrc
#guard parse mixedSrc == .ok mixedNet
#guard parse (print mixedNet) == .ok mixedNet
#guard parse (print (ofCirc t4 "t4")) == .ok (ofCirc t4 "t4")
#guard parse (print (ofCirc helloCirc)) == .ok (ofCirc helloCirc)
#guard parse "" == .ok {}

/-! ### 2. The hello file denotes asteroid's hello circuit -/

#guard read helloSrc == .ok helloCirc

/-! ### 3. Round trip `toCirc ∘ ofCirc` -/

#guard toCirc (ofCirc helloCirc) == .ok helloCirc
#guard toCirc (ofCirc t4) == .ok t4
#guard read (print (ofCirc t4 "t4")) == .ok t4

/-! ### 4. Sorting and `BUFF` -/

-- placed in the order n, o, z: `w` is an alias of `o` and is not a gate
#guard toCirc mixedNet == .ok ⟨2, [], [4], [⟨2, 0, 0⟩, ⟨1, 0, 1⟩, ⟨0, 2, 3⟩]⟩

/-! ### 5. Errors -/

#guard failsWith (read "INPUT(a)\nINPUT(b)\nOUTPUT(z)\nz = NAND(a, b)\n")
  "line 4: z = NAND(a, b): operator NAND is not accepted"
#guard failsWith (read "INPUT(a)\nOUTPUT(z)\nz = DFF(a)\n") "line 3: z = DFF(a): operator DFF"
#guard failsWith (read "INPUT(a)\nINPUT(b)\nINPUT(c)\nOUTPUT(z)\n\nz = AND(a, b, c)\n")
  "line 6: z = AND(a, b, c): AND takes exactly 2 operands, found 3"
#guard failsWith (read "INPUT(a)\nOUTPUT(z)\nz = NOT(a, a)\n") "NOT takes exactly 1 operand"
#guard failsWith (read "INPUT(a)\nOUTPUT(z)\nz = OR(a, q)\n") "line 3: z = OR(a, q): signal q"
#guard failsWith (read "INPUT(a)\nOUTPUT(z)\nz = OR(a, y)\ny = NOT(z)\n") "is on a cycle"
#guard failsWith (read "INPUT(a)\nOUTPUT(z)\n") "output z is never defined"
#guard failsWith (read "INPUT(a)\nINPUT(a)\n") "input a is declared twice"
#guard failsWith (read "INPUT(a)\nz = NOT(a)\nz = NOT(a)\n") "line 2: signal z is assigned twice"
#guard failsWith (read "INPUT(a)\na = NOT(a)\n") "is an input and is also assigned"
#guard failsWith (parse "INPUT(a)\n#@ and a = a\n") "line 2: unknown directive '#@ and'"
#guard failsWith (parse "#@ or z =\n") "line 1: directive '#@ or': no inputs"
#guard failsWith (parse "INPUT(a)\nz = NOT(a\n") "line 2: expected operands"
#guard failsWith (parse "INPUT(a)\nz == NOT(a)\n") "line 2:"
#guard failsWith (parse "INPUT(a-b)\n") "line 1: unexpected character"
#guard failsWith (parse "MODULE(a)\n") "line 1: expected INPUT(NAME)"
#guard failsWith (read "INPUT(a)\nINPUT(b)\nOUTPUT(z)\nOUTPUT(a)\n#@ or z = a b\nz = OR(a, b)\n")
  "output a has no '#@ or' directive"
#guard failsWith
  (read "INPUT(a)\nINPUT(b)\nOUTPUT(z)\n#@ or y = a b\n#@ or z = a b\nz = OR(a, b)\n")
  "y is not declared with OUTPUT(y)"
#guard failsWith (read "INPUT(a)\nINPUT(b)\nOUTPUT(z)\n#@ or z = a z\nz = OR(a, b)\n")
  "z is not an input"

/-! ### 6. AIGER export -/

#guard toAag helloCirc == "aag 7 4 0 2 3\n2\n4\n6\n8\n13\n15\n10 5 3\n12 10 7\n14 9 7\n"
-- AND stays one and, NOT is the odd literal of its operand
#guard toAag ⟨2, [], [4], [⟨2, 0, 0⟩, ⟨1, 0, 1⟩, ⟨0, 2, 3⟩]⟩ ==
  "aag 4 2 0 1 2\n2\n4\n8\n6 5 3\n8 7 3\n"

end AsteroidLang.Bench.Test
