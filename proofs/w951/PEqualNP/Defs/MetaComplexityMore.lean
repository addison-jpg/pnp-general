import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.MetaComplexityLgp
import Mathlib.Data.Nat.Log
import PEqualNP.Defs.MetaComplexity
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Nat
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup
import PEqualNP.Defs.CircuitLowerBounds

section MetaComplexityCoverCircuit

/-!
# The cover circuit, for the meta-complexity program

An explicit circuit for the function "some owner `t` is true together with one of the inputs on
its list": for each owner one block of gates (a chain of ORs over its list, then one AND with the
owner), and one more OR per block after the first, joining the blocks. With owners the members
of a vertex cover and each edge listed at one of its ends in the cover, this is a circuit for
the edge function of the graph with (number of edges) + (number of owners) - 1 gates when every
owner list is nonempty. It has no NOT gate. Owners with an empty list are skipped.

The gate list is a function of the number of inputs and of the owner lists alone, so it can be
written down by a machine: this is the circuit the reduction to the last-gate problem outputs.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The block of one owner `t` with list `v1 :: rest`, placed from wire `B` on: `rest.length`
OR gates accumulating `v1, rest`, then the AND of `t` with the accumulated OR, then, unless this
is the leading block, one OR joining the AND with wire `a` (the output of the blocks before). -/
def blockGates (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) : List Gate :=
  (List.range rest.length).map (fun i =>
      ⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩) ++
    ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])

/-- The gates of all blocks, placed from wire `B` on. `lead` says whether the next nonempty
block is the first one; `a` is the wire holding the output of the blocks before. An owner with
an empty list contributes no gate. -/
def coverGatesB (B : ℕ) (lead : Bool) (a : ℕ) : List (ℕ × List ℕ) → List Gate
  | [] => []
  | (_, []) :: os => coverGatesB B lead a os
  | (t, v1 :: rest) :: os =>
      blockGates B a t v1 rest lead ++
        coverGatesB (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) os

/-- The cover circuit on `n` inputs for the owner lists `own`: the gates of all blocks, placed
from wire `n` on, with the last gate as output. With no gate at all it is the circuit with no
gate whose output wire does not exist, the constant `false`. -/
def coverCircuitB (n : ℕ) (own : List (ℕ × List ℕ)) : Circuit :=
  if coverGatesB n true 0 own = [] then ⟨[], n⟩
  else ⟨coverGatesB n true 0 own, n + (coverGatesB n true 0 own).length - 1⟩

end PEqualNP.MetaComplexity

end MetaComplexityCoverCircuit

section MetaComplexityLgpMono

/-!
# The monotone last-gate problem, for the meta-complexity program

The same problem as in `PEqualNP.Defs.MetaComplexityMinimal` and `PEqualNP.Defs.MetaComplexityLgp`
with NOT gates forbidden on both sides: circuits use AND and OR gates of fan-in at most two, and
minimality is among such circuits only. Instances are written as strings by the same `encodeLgp`.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The circuit uses only AND and OR gates, each reading at most two wires: `FanInTwo` without
NOT. An AND gate reading no wire is the constant `true` and an OR gate reading no wire is the
constant `false`; a gate reading one wire copies it. -/
def Monotone2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- `C` is a minimal monotone circuit on `n` inputs: it uses AND and OR gates of fan-in at most
two, and every circuit of that kind computing the same function on `n` inputs has at least as
many gates. Every gate counts, constant gates included; inputs are not counted. -/
def IsMinimalMonoCircuit (n : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size

/-- `C` is near-minimal among monotone circuits on `n` inputs: fan-in two AND, OR, and at most
one gate more than any such circuit computing the same function on `n` inputs. -/
def NearMinimalMono (n : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size + 1

/-- The YES side of the monotone last-gate problem on `n` inputs: the minimal monotone circuits. -/
def MonoLgpYes (n : ℕ) (C : Circuit) : Prop := IsMinimalMonoCircuit n C

/-- The NO side: near-minimal among monotone circuits and not minimal among them, that is,
exactly one gate above the monotone minimum. -/
def MonoLgpNo (n : ℕ) (C : Circuit) : Prop := NearMinimalMono n C ∧ ¬ IsMinimalMonoCircuit n C

/-- The monotone last-gate problem is in P, as a promise problem, on the same instance code as
`LgpInP`: some test computable in time polynomial in the length of `encodeLgp (n, C)` answers
`true` on every minimal monotone circuit and `false` on every monotone circuit exactly one gate
above the monotone minimum, on `n` inputs. Nothing is required on any other instance. -/
def MonoLgpInP : Prop :=
  ∃ f : ℕ × Circuit → Bool,
    PEqualNP.Library.ComputableInPolyTime encodeLgp Computability.encodeBool f ∧
      ∀ p : ℕ × Circuit, (MonoLgpYes p.1 p.2 → f p = true) ∧ (MonoLgpNo p.1 p.2 → f p = false)

end PEqualNP.MetaComplexity

end MetaComplexityLgpMono

section MetaComplexityLocal

/-!
# Local maps, for the meta-complexity program

One definition: a map on `n`-bit inputs every output position of which is fixed by few input
positions. It is the only notion of a local reduction the program's statements use; it speaks
of no machine. The ruling behind it is in `MetaComplexity/README.md`.
-/

namespace PEqualNP.MetaComplexity

/-- The map `w` on inputs of length `n` is `q`-local: for every output position `j` and every
input `x` there are at most `q` input positions such that every input agreeing with `x` on them
has the same symbol at position `j` of its output (the same bit, or in both cases no bit, so
the output length may vary with the input). This is "certificate complexity at most `q`" of
every output position. It is implied by: position `j` of the output is computed in `q` steps
with random access to the input. A statement that assumes only this is therefore stronger than
one about reductions computable in local time `q`. -/
def QueryLocal (n q : ℕ) (w : (Fin n → Bool) → List Bool) : Prop :=
  ∀ (j : ℕ) (x : Fin n → Bool), ∃ S : Finset (Fin n), S.card ≤ q ∧
    ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → (w y)[j]? = (w x)[j]?

end PEqualNP.MetaComplexity

end MetaComplexityLocal

section MetaComplexitySparse

/-!
# Sparse partial MCSP, for the meta-complexity program

Partial MCSP with the partial truth table given as a list of rows, not as a table of length
`2 ^ n`. A row is a point of `{0,1}^m` and the value the function must take there. Circuits and
their size are those of `PEqualNP.Defs.MetaComplexity` (`HasCircuitSize`). Nothing here speaks
of machines.
-/

namespace PEqualNP.MetaComplexity

/-- The binary code of a list of rows on `m` variables: each row `(x, b)` is written as the `m`
bits `x 0, ..., x (m - 1)` followed by the value `b`, so `m + 1` bits per row, rows in order. -/
def encodeRows (m : ℕ) (rows : List ((Fin m → Bool) × Bool)) : List Bool :=
  rows.flatMap fun r : (Fin m → Bool) × Bool => List.ofFn r.1 ++ [r.2]

/-- Sparse partial MCSP, the minimum circuit size problem for a partial function given as a list
of rows, as a language over `Bool`. An instance is a size bound `s` in unary (`s` times `true`),
one `false`, the number of variables `m` in unary (`m` times `true`), one `false`, then the code
`encodeRows m rows` of a list of rows. It is a member when some total function on `m` variables
that takes the value `b` at `x` for every row `(x, b)` has a circuit with at most `s` gates.
Rows may repeat; two rows with the same point and different values admit no such function, so
the instance is not a member. A string of any other shape is not a member. The numbers `s`, `m`
and the list of rows are determined by the string. -/
def SparsePartialMCSP : Language Bool :=
  {w | ∃ (m s : ℕ) (rows : List ((Fin m → Bool) × Bool)),
    w = List.replicate s true ++ false :: (List.replicate m true ++ false :: encodeRows m rows) ∧
      ∃ f : (Fin m → Bool) → Bool, (∀ r ∈ rows, f r.1 = r.2) ∧ HasCircuitSize m f s}

end PEqualNP.MetaComplexity

end MetaComplexitySparse

section MetaComplexityTypedRank

/-!
# Typed rank of a Boolean function

Let `f` be a Boolean function on `n` inputs. A pair is an input `x` with `f x = true` together
with an input `y` with `f y = false`. A typing gives every pair a position at which the two
inputs differ. A literal is a position `i` with a bit `b`; the pair `(x, y)` has the literal
`(i, b)` when its position is `i` and `x i = b` (so `y i` is the other bit). For each literal
take the 0/1 matrix of the pairs having it. The typed rank of `f` is the least, over all
typings, of the sum over the `2 * n` literals of the ranks of these matrices over the rationals.

It is a restricted form of span program size: there the matrices of the literals may have any
entries and overlapping supports; here they are 0/1 with disjoint supports.

* `IsTyping n f τ`: `τ` is a typing of `f`.
* `typedMatrix n f τ i b`: the matrix of the pairs having the literal `(i, b)`.
* `HasTypedRank n f s`: some typing has rank sum at most `s`.

Nothing here speaks of formulas; the module imports only Mathlib.
-/

namespace PEqualNP.MetaComplexity

/-- `τ` is a typing of `f`: for every input `x` with `f x = true` and every input `y` with
`f y = false`, the number `τ x y` is a position `i` below `n` at which `x` and `y` differ. The
values of `τ` at other arguments are not constrained and are never used. The values are
natural numbers, not elements of `Fin n`, so that a typing exists when `n = 0` (then `f` is
constant and there is no pair to type). -/
def IsTyping (n : ℕ) (f : (Fin n → Bool) → Bool)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) : Prop :=
  ∀ x y : Fin n → Bool, f x = true → f y = false →
    ∃ i : Fin n, τ x y = (i : ℕ) ∧ x i ≠ y i

/-- The matrix of the literal `(i, b)` under `τ`: rows and columns are all inputs; the entry at
`(x, y)` is `1` when `f x = true`, `f y = false`, `τ x y = i` and `x i = b`, and `0` otherwise.
Rows of inputs where `f` is false and columns of inputs where `f` is true are zero, so the rank
is that of the matrix restricted to the pairs. -/
def typedMatrix (n : ℕ) (f : (Fin n → Bool) → Bool)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (i : Fin n) (b : Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun x y => if f x = true ∧ f y = false ∧ τ x y = (i : ℕ) ∧ x i = b then 1 else 0

/-- `f` has typed rank at most `s`: there is a typing of `f` for which the ranks, over the
rationals, of the `2 * n` literal matrices sum to at most `s`. -/
def HasTypedRank (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ τ : (Fin n → Bool) → (Fin n → Bool) → ℕ, IsTyping n f τ ∧
    (∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank) ≤ s

end PEqualNP.MetaComplexity

end MetaComplexityTypedRank

section BinaryCircuit

/-!
# Circuits over all two-input gates, for the meta-complexity program

A binary circuit is a list of gates; each gate is a Boolean function of two arguments together
with the indices of the two wires it reads. Evaluation follows the root `Circuit` exactly:
wires `0` to `n - 1` are the inputs, gate number `j` (from `0`) produces wire `n + j`, a wire
that does not exist (yet) reads `false`, and the value of the circuit is the value of its
output wire (`false` if there is none). Size is the number of gates; inputs are not counted.

Every gate counts, also a gate that negates or copies one wire or ignores both (a constant).
So the constant `false` has size zero (an output wire that does not exist) and the constant
`true` has size one, as on the root.
-/


namespace PEqualNP.MetaComplexity

/-- A gate over the full binary basis: any function of two Boolean arguments, and the indices
of the two wires it reads. -/
structure BinaryGate where
  /-- The operation: any of the sixteen Boolean functions of two arguments. -/
  op : Bool → Bool → Bool
  /-- The index of the wire read as the left argument. -/
  left : ℕ
  /-- The index of the wire read as the right argument. -/
  right : ℕ

/-- A circuit over the full binary basis: its gates in evaluation order and the index of its
output wire. -/
structure BinaryCircuit where
  /-- The gates. Gate number `j` (from `0`) produces wire `(input length) + j`. -/
  gates : List BinaryGate
  /-- The index of the output wire. -/
  output : ℕ

/-- The values of all wires on input `x`: the bits of `x`, then one value per gate. A wire
that does not exist when a gate is evaluated reads `false`. -/
def BinaryCircuit.wires (C : BinaryCircuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

/-- The value of the circuit on input `x`: the value of its output wire, `false` if there is
none. -/
def BinaryCircuit.eval (C : BinaryCircuit) (x : List Bool) : Bool :=
  (C.wires x).getD C.output false

/-- The size: the number of gates. -/
def BinaryCircuit.size (C : BinaryCircuit) : ℕ :=
  C.gates.length

/-- The function `f` on `n` inputs has a circuit over the full binary basis with at most `s`
gates. The parallel of `HasCircuitSize`, with every two-input gate allowed. -/
def HasBinarySize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : BinaryCircuit, C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

end PEqualNP.MetaComplexity

end BinaryCircuit

section PendantBit

/-!
# The pendant bit of a Boolean function at an input

For a Boolean function `f` on `n` inputs and an input `v`, the PENDANT FUNCTION `pendF n f v` is
the function on `n + 1` inputs `f(x) OR (x_v AND y)`, where `y` is the fresh LAST input
(`Fin.last n`) and the old inputs are read through `Fin.castSucc`. The PENDANT BIT is the integer

  `pendantBit n f v = size(f) + 2 - size(pendF n f v)`,

where `size` is the least number of gates of a circuit computing the function, in the model of
`PEqualNP.MetaComplexity.HasCircuitSize`: AND, OR and NOT gates reading at most two wires, every
gate counted (NOT gates and constant gates included), inputs free.

* `minCircuitSize n f`: the least `s` with `HasCircuitSize n f s`.
* `pendF n f v`: the pendant function `f(x) OR (x_v AND y)` on `n + 1` inputs.
* `pendantBit n f v`: the pendant bit, an integer.

Caveats a statement must respect.
* The size model is `HasCircuitSize`, NOT the strict model `PEqualNP.MinimumComplex.cc`. They
  price constants differently: here the constant `false` has size `0` (an output wire that does
  not exist reads `false`) and the constant `true` has size `1` (an AND gate reading no wire);
  in the strict model both cost `2` gates on `n ≥ 1` inputs, and `cc` is `0` at `n = 0`. Here
  gates may also read one wire twice, read one wire only, or read no wire. On paper the two
  sizes agree on non-constant functions of `n ≥ 1` inputs (a least circuit needs no constant
  and no repeated or copying gate); that agreement is NOT stated here. This model is chosen
  because it reproduces the concept's non-examples (constant `false` has bit `1`; it would be
  `3` in the strict model).
* `minCircuitSize` is `sInf` of a set of naturals. The set is never empty (every function has a
  circuit: `PEqualNP.CircuitLowerBounds.Helpers.hasCircuitSize_all`), so the infimum is
  attained; the definition itself does not rely on that.
* The bit is an integer, subtraction in `ℤ`. It is NOT always `0` or `1`: constant `true` and
  `f = x_v` give `2`, constant `false` gives `1`. "The bit is `0` or `1`" is a theorem under
  hypotheses (`f` non-constant and `f x = false` for some `x` with `x_v = true`), never part of
  the definition.
-/

namespace PEqualNP.PendantBit

open PEqualNP.MetaComplexity

/-- The least number of gates of a circuit of AND, OR and NOT gates of fan-in at most two
computing `f` on `n` inputs (every gate counted, inputs free), as `sInf` over
`HasCircuitSize`. -/
noncomputable def minCircuitSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {s | HasCircuitSize n f s}

/-- The pendant function of `f` at the input `v`: on `n + 1` inputs, `f` of the first `n`
inputs, OR the AND of input `v` with the fresh last input `Fin.last n`. -/
def pendF (n : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n) : (Fin (n + 1) → Bool) → Bool :=
  fun x => f (fun i => x i.castSucc) || (x v.castSucc && x (Fin.last n))

/-- The pendant bit of `f` at `v`: `size(f) + 2 - size(pendF n f v)`, in the integers. -/
noncomputable def pendantBit (n : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n) : ℤ :=
  (minCircuitSize n f : ℤ) + 2 - (minCircuitSize (n + 1) (pendF n f v) : ℤ)

end PEqualNP.PendantBit

end PendantBit

section MinimumComplex

/-!
# The minimum complex of a Boolean function

Circuits are the root circuits of `PEqualNP.Defs.CircuitLowerBounds` (straight-line programs,
wires `0` to `n - 1` are the inputs, gate number `j` produces wire `n + j`), restricted to the
STRICT model of this concept: every gate is an AND or an OR reading exactly two distinct earlier
wires, or a NOT reading exactly one earlier wire. Every gate counts, inputs are free. A circuit
computes `f` when it is strict, its output is one of its wires, and its value is `f`.

A minimum circuit of `f` determines the SET of functions its gates compute (its gate set). The
MINIMUM COMPLEX `M(f)` is the simplicial complex whose maximal faces (facets) are exactly the
gate sets of the minimum circuits of `f`. It is represented by PREDICATES on finite sets of
functions: `IsFacet n f S` (maximal faces) and `IsFace n f S` (all faces); vertices are the
useful functions. A vertex is FORCED when it lies in every facet; the REDUCED complex deletes the
forced vertices from every facet.

The ONE-ABOVE family `M_1(f)`: gate sets of strict circuits of `f` with `cc f + 1` gates whose
gate functions are pairwise distinct, none an input and none a constant. Such a set is PADDED if
it contains a facet of `M(f)`. Two one-above sets are joined at window `k` when they share at
least `cc f + 1 - k` functions (one step replaces at most `k` functions). The ESCAPE WINDOW is
the least `k` such that from every one-above set some padded one is reached by such steps.

* `BoolFun n`: Boolean functions of `n` inputs.
* `StrictGate w g`, `Strict n C`: the gate model (AND, OR on two distinct earlier wires, NOT on
  one), as a condition on root circuits.
* `Computes n f C`: `C` is strict, its output is a wire, and it computes `f`.
* `cc n f`: the least size of a circuit computing `f`.
* `IsMinCircuit n f C`: `C` computes `f` and no circuit computing `f` is smaller.
* `gateFun n C j`, `gateSet n C`: the function of gate `j`, the set of all gate functions.
* `IsFacet n f S`, `IsFace n f S`, `IsUseful n f g`: facets, faces and vertices of `M(f)`.
* `IsForced n f g`: a vertex lying in every facet.
* `IsReducedFacet n f R`: `R` is a facet with the forced vertices removed.
* `IsInputFun n g`, `IsConstFun g`: trivial functions.
* `IsOneAboveFacet n f S`, `IsPadded n f S`: the one-above family and its padded sets.
* `FlipAdj n f k S T`: one-above sets sharing at least `cc f + 1 - k` functions.
* `EscapesWithin n f k`, `escapeWindow n f`: every one-above set reaches a padded one at
  window `k`; the least such `k`.

Caveats a statement must respect.
* The intended hypothesis is that `f` is neither constant nor an input. For an input `f` the
  minimum circuit has no gate and the only facet is the empty set. For `n = 0` no circuit has a
  wire, nothing computes anything and `cc` is `sInf` of the empty set, that is `0`.
* A facet is a set of FUNCTIONS, not a circuit: circuits with different wiring may give the same
  facet, and duplicate gate functions collapse in `gateSet` (they do not occur in minimum
  circuits of non-constant non-input functions, a paper fact not stated here).
* `cc` and `escapeWindow` are `sInf` of sets of naturals: `0` when the set is empty (`escapeWindow`
  is also `0` when the one-above family is empty).
* `IsReducedFacet` of a rigid function (one facet) is the empty set, the empty face.
* The strict size `cc` is not the main size of the project (`HasCircuitSize`, and its infimum
  `PEqualNP.PendantBit.minCircuitSize`). They differ on the constants: for `n ≥ 1` a strict
  circuit needs 2 gates for a constant, the main size is 0 for constant false and 1 for constant
  true. A sanity helper shows only one direction, main size at most `cc`.
* `escapeWindow n f = 0` covers three different situations: every one-above set is already
  padded; there is no one-above set; and no window works at all (`sInf` of the empty set). A
  statement about the window must say which case it excludes.
-/

namespace PEqualNP.MinimumComplex

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The Boolean functions of `n` inputs. -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- The gate `g`, placed where `w` wires exist (wires `0` to `w - 1`), is strict: an AND or an
OR reading exactly two distinct existing wires, or a NOT reading exactly one existing wire. -/
def StrictGate (w : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
      ∀ i ∈ g.inputs, i < w) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1 ∧ ∀ i ∈ g.inputs, i < w)

/-- The circuit `C` on `n` inputs is strict: gate number `j` (wire `n + j`) is a strict gate
reading only the `n + j` wires before it. -/
def Strict (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (h : j < C.gates.length), StrictGate (n + j) C.gates[j]

/-- `C` computes `f` on `n` inputs in the strict model: `C` is strict, its output is one of its
wires (an input or a gate), and its value on every input is that of `f`. -/
def Computes (n : ℕ) (f : BoolFun n) (C : Circuit) : Prop :=
  Strict n C ∧ C.output < n + C.size ∧ circuitFun n C = f

/-- The circuit complexity of `f` in the strict model: the least size of a circuit computing
it (`0` if none does, which happens only for `n = 0`). -/
noncomputable def cc (n : ℕ) (f : BoolFun n) : ℕ :=
  sInf {s | ∃ C : Circuit, Computes n f C ∧ C.size = s}

/-- `C` is a minimum circuit of `f`: it computes `f` and every circuit computing `f` has at least
as many gates. -/
def IsMinCircuit (n : ℕ) (f : BoolFun n) (C : Circuit) : Prop :=
  Computes n f C ∧ ∀ D : Circuit, Computes n f D → C.size ≤ D.size

/-- The function computed by gate number `j` of `C` (wire `n + j`) on `n` inputs. -/
def gateFun (n : ℕ) (C : Circuit) (j : ℕ) : BoolFun n :=
  fun x => (C.wires (List.ofFn x)).getD (n + j) false

/-- The gate set of `C` on `n` inputs: the set of the functions its gates compute. -/
def gateSet (n : ℕ) (C : Circuit) : Finset (BoolFun n) :=
  (Finset.range C.size).image (gateFun n C)

/-- `S` is a facet (maximal face) of the minimum complex `M(f)`: the gate set of a minimum
circuit of `f`. -/
def IsFacet (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ C : Circuit, IsMinCircuit n f C ∧ gateSet n C = S

/-- `S` is a face of `M(f)`: a subset of a facet. -/
def IsFace (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ T, IsFacet n f T ∧ S ⊆ T

/-- `g` is a vertex of `M(f)` (a useful function of `f`): it lies in some facet. -/
def IsUseful (n : ℕ) (f : BoolFun n) (g : BoolFun n) : Prop :=
  ∃ S, IsFacet n f S ∧ g ∈ S

/-- `g` is a forced vertex of `M(f)`: a vertex lying in every facet. -/
def IsForced (n : ℕ) (f : BoolFun n) (g : BoolFun n) : Prop :=
  IsUseful n f g ∧ ∀ S, IsFacet n f S → g ∈ S

/-- `R` is a facet of the reduced complex: some facet of `M(f)` with its forced vertices
removed. -/
def IsReducedFacet (n : ℕ) (f : BoolFun n) (R : Finset (BoolFun n)) : Prop :=
  ∃ S, IsFacet n f S ∧ ∀ g, g ∈ R ↔ g ∈ S ∧ ¬ IsForced n f g

/-- `g` is an input: `g x = x i` for some `i`. -/
def IsInputFun (n : ℕ) (g : BoolFun n) : Prop :=
  ∃ i : Fin n, g = fun x => x i

/-- `g` is a constant function. -/
def IsConstFun {n : ℕ} (g : BoolFun n) : Prop :=
  ∃ b : Bool, g = fun _ => b

/-- `S` is a facet of the one-above family `M_1(f)`: the gate set of a strict circuit computing
`f` with `cc f + 1` gates whose gate functions are pairwise distinct (as many functions as
gates), none an input and none a constant. -/
def IsOneAboveFacet (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ C : Circuit, Computes n f C ∧ C.size = cc n f + 1 ∧ (gateSet n C).card = C.size ∧
    (∀ g ∈ gateSet n C, ¬ IsInputFun n g ∧ ¬ IsConstFun g) ∧ gateSet n C = S

/-- A one-above set is padded when it contains a facet of `M(f)`. -/
def IsPadded (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  IsOneAboveFacet n f S ∧ ∃ T, IsFacet n f T ∧ T ⊆ S

/-- The flip graph of `M_1(f)` at window `k`: two one-above sets sharing at least
`cc f + 1 - k` functions (one step replaces at most `k` functions). -/
def FlipAdj (n : ℕ) (f : BoolFun n) (k : ℕ) (S T : Finset (BoolFun n)) : Prop :=
  IsOneAboveFacet n f S ∧ IsOneAboveFacet n f T ∧ cc n f + 1 ≤ (S ∩ T).card + k

/-- At window `k` every one-above set reaches a padded one by flip steps. -/
def EscapesWithin (n : ℕ) (f : BoolFun n) (k : ℕ) : Prop :=
  ∀ S, IsOneAboveFacet n f S →
    ∃ T, Relation.ReflTransGen (FlipAdj n f k) S T ∧ IsPadded n f T

/-- The escape window of `f`: the least window at which every one-above set reaches a padded
one (`0` if there is none, by `sInf`). -/
noncomputable def escapeWindow (n : ℕ) (f : BoolFun n) : ℕ :=
  sInf {k | EscapesWithin n f k}

end PEqualNP.MinimumComplex

end MinimumComplex

section SingleLevel

/-!
# Single-level circuits for the selector family `f_H`, for the meta-complexity program

The graph. A graph on the vertices `Fin v` is a list of edges (ordered pairs). The order of the
list indexes the selector inputs. `WF` says the list is a simple graph: no loop, no edge listed
twice in either orientation.

Covers. A vertex cover is a set of vertices meeting every edge; the cover number `vc` is the
least size of a vertex cover.

The excess `ex`: the largest value of `|F| - |V(F)|` over sub-lists `F` of the edge list, where
`V(F)` is the set of vertices the edges of `F` touch (truncated subtraction; the empty sub-list
gives `0`).

The input layout of `fH E` on a graph with `v` vertices and edge list `E` (`m = E.length`):
wire `0` is `x_0`; wire `1 + u` is the vertex variable `x_u` (`u < v`); wire `1 + v + i` is the
selector `z_i` of the edge `E[i]` (`i < m`). So `n = 1 + v + m` inputs.

The selector function: `f_H = OR over edges e = uv of (z_e AND (x_0 OR x_u OR x_v))`.

The class: fan-in two AND/OR/NOT circuits (`FanInTwo`) with no NOT gate, in which every wire has
AND depth at most `1`. Only an AND gate reading at least two wires counts as a level. `IsLeastSL`
says a circuit of the class computes `f` and has no more gates than any circuit of the class
computing `f`.

Circuits, their size and the function they compute are those of
`PEqualNP.Defs.CircuitLowerBounds`, `PEqualNP.Defs.MetaComplexity` and
`PEqualNP.Defs.MetaComplexityMinimal`.
-/

namespace PEqualNP.MetaComplexity.SingleLevel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## The graph side -/

/-- A graph on the vertices `Fin v`, given by its list of edges. The order of the list
fixes the order of the selector inputs. -/
abbrev Edges (v : ℕ) := List (Fin v × Fin v)

/-- Two ordered pairs name the same undirected edge. -/
def SameEdge {v : ℕ} (e f : Fin v × Fin v) : Prop :=
  (e.1 = f.1 ∧ e.2 = f.2) ∨ (e.1 = f.2 ∧ e.2 = f.1)

instance {v : ℕ} (e f : Fin v × Fin v) : Decidable (SameEdge e f) := by
  unfold SameEdge; infer_instance

/-- The edge list is a simple graph: no loop, no edge listed twice in either
orientation. -/
def WF {v : ℕ} (E : Edges v) : Prop :=
  (∀ e ∈ E, e.1 ≠ e.2) ∧ E.Pairwise (fun e f => ¬ SameEdge e f)

instance {v : ℕ} (E : Edges v) : Decidable (WF E) := by unfold WF; infer_instance

/-- `T` is a vertex cover: every edge has an end in `T`. -/
def IsCover {v : ℕ} (E : Edges v) (T : Finset (Fin v)) : Prop :=
  ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T

instance {v : ℕ} (E : Edges v) (T : Finset (Fin v)) : Decidable (IsCover E T) := by
  unfold IsCover; infer_instance

/-- The vertex cover number: the least size of a vertex cover (the set of all vertices
is one, so the set below is nonempty). -/
noncomputable def vc {v : ℕ} (E : Edges v) : ℕ :=
  sInf {k | ∃ T : Finset (Fin v), IsCover E T ∧ T.card = k}

/-- The vertices touched by a list of edges, as a list without repetition. -/
def verts {v : ℕ} (F : Edges v) : List (Fin v) :=
  (F.flatMap fun e => [e.1, e.2]).dedup

/-- The excess, in a component-free form: the largest value of `|F| - |V(F)|` over
sub-lists `F` of the edge list (truncated subtraction; the empty sub-list gives `0`). -/
def ex {v : ℕ} (E : Edges v) : ℕ :=
  (E.sublists.map fun F => F.length - (verts F).length).foldr max 0

/-! ## The function -/

/-- The input wire of `x_0`. -/
def x0 {v m : ℕ} : Fin (1 + v + m) := ⟨0, by omega⟩

/-- The input wire of the vertex variable `x_u`. -/
def xv {v m : ℕ} (u : Fin v) : Fin (1 + v + m) := ⟨1 + u.val, by omega⟩

/-- The input wire of the selector `z_i` of edge number `i`. -/
def zs {v m : ℕ} (i : Fin m) : Fin (1 + v + m) := ⟨1 + v + i.val, by omega⟩

/-- The selector family: `f_H = OR over edges e = uv of (z_e AND (x_0 OR x_u OR x_v))`,
on `1 + v + m` inputs in the layout of the module docstring. -/
def fH {v : ℕ} (E : Edges v) (y : Fin (1 + v + E.length) → Bool) : Bool :=
  (List.finRange E.length).any fun i =>
    y (zs i) && (y x0 || y (xv (E.get i).1) || y (xv (E.get i).2))

/-! ## The circuit class -/

/-- The AND level a gate adds: `1` for an AND gate reading at least two wires, else `0`.
An AND gate reading no wire (the constant `true`) or one wire (a copy) adds no level; an AND
gate reading one wire twice (`[j, j]`) does. -/
def andLevel (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, _ :: _ :: _ => 1
  | _, _ => 0

/-- The AND depth of every wire on `n` inputs: the largest number of (two-input) AND
gates on a path ending at the wire. Inputs `0`; a gate: the largest AND depth among the wires
it reads (a wire that does not exist counts `0`), plus its `andLevel`. Same fold as
`Circuit.depths`. -/
def andDepths (C : Circuit) (n : ℕ) : List ℕ :=
  C.gates.foldl
    (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + andLevel g])
    (List.replicate n 0)

/-- The gate is not a NOT gate. -/
def notNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

/-- The class: fan-in two AND/OR/NOT (`FanInTwo`), no NOT gate, and every wire (dead
gates included) has AND depth at most `1`: no path passes through two two-input AND gates. -/
def IsSingleLevel (n : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧ (∀ g ∈ C.gates, notNot g = true) ∧ ∀ d ∈ andDepths C n, d ≤ 1

/-- `C` is a least circuit of `f` inside the class. -/
def IsLeastSL (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  IsSingleLevel n C ∧ circuitFun n C = f ∧
    ∀ D : Circuit, IsSingleLevel n D → circuitFun n D = f → C.size ≤ D.size

end PEqualNP.MetaComplexity.SingleLevel

end SingleLevel
