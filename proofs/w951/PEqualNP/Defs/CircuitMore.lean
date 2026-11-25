import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.BlindGate
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.LineDegree
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.WithBot
import PEqualNP.Defs.PencilGate
import PEqualNP.Defs.EdgeOwnership

section AndCountCircuit

/-!
# AND-count circuits on a vertex set

The monotone circuits of the AND-count family (cover-bound rows), with OR free. An AND-count
circuit on the vertex set `Fin n` is a list of `size` gates, each the AND of two SIDES. A side
is a pair `(B, F)`: a finite set `B` of vertices (its bare variables) and a finite set `F` of
gates (it reads gate `j` as an OR summand). The output is the OR of a set of vertices and a set
of gates. Value at a set `U` of true variables: a side is true iff `B` meets `U` or some gate
of `F` is true; a gate is true iff both its sides are; the circuit is true iff some output
vertex lies in `U` or some output gate is true. The size is the number of gates, i.e. the
number of AND gates (OR costs nothing).

The circuit COMPUTES the edge function of a graph `G` if its value at `U` is true exactly when
`U` contains both ends of an edge.

* `AndCountCircuit n`: the data (size, the two sides of each gate, the output).
* `AndCountCircuit.WellFormed`: every gate read by a side of gate `i` comes before `i`.
* `AndCountCircuit.sideTrue`, `AndCountCircuit.gateValFuel`, `AndCountCircuit.gateVal`: the
  value of a side, of a gate (by recursion on a fuel bounded by the size), at a set `U`.
* `AndCountCircuit.eval`: the value of the circuit at `U`.
* `AndCountCircuit.Computes`: the circuit computes the edge function of `G`.
* `AndCountCircuit.starCircuit`: the star circuit of a vertex set `T`, one gate per member
  `t` with sides `({t}, none)` and `(N(t), none)`, every gate an output.

Caveats for statements.
* Only `WellFormed` circuits are circuits. The evaluator reads gate `j` from gate `i` only
  when `j < i` (a later or equal index named by a side is ignored, not an error), so a
  statement about circuits must assume `WellFormed`: a gate naming a later gate is the
  thinker's non-circuit.
* The output may name vertices as well as gates (the normal form of the filer, rows L-meta-349
  ff., with `OV` and `OG`). A circuit computing the edge function of any graph has no output
  vertex (the singleton of that vertex contains no edge), so for computing circuits this is the
  thinker's "set of output gates". The output set is NOT required to be nonempty: the empty
  circuit (size 0, empty output) computes the edge function of an edgeless graph, and is the
  star circuit of the empty cover.
* Sides may be empty, and the two sides of a gate may share vertices (a side's vertices form a
  finite set, so a vertex appears in a side at most once); no normal form (nonempty, disjoint,
  unit-free) is built in. State such hypotheses explicitly.
* Every circuit is false at the empty set, so no circuit computes the constant true function.
* Size is `size`, the AND count; it is not the gate count of `Defs/CircuitLowerBounds`.
* No 4-cycle condition is built in: on the 4-cycle one gate computes the edge function while
  the cover number is 2, so the family's statements assume girth at least 5 themselves.
-/

namespace PEqualNP.AndCount

/-- An AND-count circuit on the vertex set `Fin n`: `size` gates, gate `i` the AND of the
side `(leftVars i, leftGates i)` and the side `(rightVars i, rightGates i)`; the output is the
OR of the vertices `outVars` and the gates `outGates`. -/
structure AndCountCircuit (n : ℕ) where
  /-- The number of gates (AND gates). -/
  size : ℕ
  /-- The bare variables of the first side of each gate. -/
  leftVars : Fin size → Finset (Fin n)
  /-- The gates read by the first side of each gate. -/
  leftGates : Fin size → Finset (Fin size)
  /-- The bare variables of the second side of each gate. -/
  rightVars : Fin size → Finset (Fin n)
  /-- The gates read by the second side of each gate. -/
  rightGates : Fin size → Finset (Fin size)
  /-- The vertices read by the output OR. -/
  outVars : Finset (Fin n)
  /-- The gates read by the output OR. -/
  outGates : Finset (Fin size)

namespace AndCountCircuit

variable {n : ℕ}

/-- Well-formed: each side of gate `i` reads only gates `j < i`. -/
def WellFormed (C : AndCountCircuit n) : Prop :=
  ∀ i : Fin C.size, (∀ j ∈ C.leftGates i, j < i) ∧ (∀ j ∈ C.rightGates i, j < i)

/-- The value of the side `(B, F)` of gate `i` at `U`, given the values `val` of the gates:
`B` meets `U`, or some gate `j ∈ F` with `j < i` is true. -/
def sideTrue {k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) : Bool :=
  decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true)

/-- The gate values at `U` computed with fuel `d` (fuel `0` gives `false`). Fuel `C.size`
suffices, since only earlier gates are read. -/
def gateValFuel (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ℕ → Fin C.size → Bool
  | 0, _ => false
  | d + 1, i =>
      sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)

/-- The value of gate `i` at the set `U` of true variables. -/
def gateVal (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  gateValFuel C U C.size i

/-- The value of the circuit at `U`: some output vertex is in `U` or some output gate is
true. -/
def eval (C : AndCountCircuit n) (U : Finset (Fin n)) : Bool :=
  decide ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true)

/-- `C` computes the edge function of `G`: its value at `U` is true exactly when `U`
contains both ends of an edge of `G`. -/
def Computes (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ U : Finset (Fin n), C.eval U = true ↔ ∃ a ∈ U, ∃ c ∈ U, G.Adj a c

/-- The star circuit of a vertex set `T`: gate `j` belongs to the `j`-th member `t` of `T` in
increasing order, with sides `({t}, none)` and `(N(t), none)`; every gate is an output. -/
def starCircuit (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) :
    AndCountCircuit n where
  size := T.card
  leftVars j := {T.orderEmbOfFin rfl j}
  leftGates _ := ∅
  rightVars j := Finset.univ.filter (fun w => G.Adj (T.orderEmbOfFin rfl j) w)
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

end AndCountCircuit

end PEqualNP.AndCount

end AndCountCircuit

section BorrowedCoverCircuit

/-!
# Borrowed cover circuits of a graph function

The setting is that of `PEqualNP.Defs.NestedCoverCircuit`: inputs `Fin n`, wire `i < n` is
`x_i`, gate number `j` is wire `n + j`, a graph `K` on `Fin n` and a set `A` of inputs give the
graph function `F_(K,A)`. A nested cover circuit is a circuit together with data (`NCCData`)
labelling every gate with its role; this module adds one local departure from it.

The object (section 2 of the borrowed cover note of the last-gate route). A BORROWING in nested
data is a quintuple `(s, t, q, r, m)` of distinct vertices (the note calls `m` "n"; here `n` is
the number of inputs) with
* (b1) `s -> t` is a tie;
* (b2) `t` is a root (no tie out of `t`) and the vertices owned by `t` are exactly `s` and `q`;
* (b3) `m` is in the cover, `m != t`, and `m` owns `ms` and `mr`;
* (b4) `rq` is an edge of `K` (so `s t q r m` is a 5-cycle);
* (b5) the leaf `lam_m(s)` is the root of `Z_s`, and some OR gate `a` of `O_m` has exactly the
  two operands `lam_m(s)` and `lam_m(r)` (in either order);
* (b6) every leaf `lam_t'(t)`, `t'` owning `t't`, is the input `x_t`.
A BORROWED COVER CIRCUIT is the circuit of nested data with a set of borrowings with pairwise
distinct `s`, in which for each borrowing the term of `s` is `B_s = AND(a, root of O_s)` in place
of `AND(root of Z_s, root of O_s)`; every other gate is as in a nested cover circuit.

The formal reading. As for nested cover circuits, the module does not generate the circuit: it
says when a given circuit IS one. The data is `BCCData n`: nested data `base` and, for each
vertex `s`, an optional borrowing `borrow s` (keyed by `s`, so the `s` are distinct by
construction) recording `t, q, r, m` and the gate index of `a`. `BValid` is `Valid` of
`NestedCoverCircuit` verbatim, except that the condition `TermOK` on the term of a borrowed `s`
is replaced by `BorrowedTermOK` (the term reads the wire of `a` in place of the root of `Z_s`),
plus the condition `IsBorrowing` on every recorded borrowing. Nothing else changes: the tree
`Z_s` is still checked as an OR tree with root `zroot s` (its root is simply no longer read by
`B_s`; the tree conditions count reads inside the tree only).

Relation to `IsNestedCoverCircuit`. With no borrowing (`borrow s = none` for all `s`), `BValid`
is exactly `Valid` on `base`; so every nested cover circuit is a borrowed cover circuit, and a
circuit is nested iff it has a borrowed labelling with no borrowing. That a labelling with at
least one borrowing is never nested (the borrowed term is an AND gate not below `F`) is Lemma B of
the note, on paper only; it is NOT part of the definition.

* `Borrow n`: the record `t, q, r, m, gate` of one borrowing (the `s` is the key).
* `BCCData n`: `base : NCCData n` and `borrow : Fin n → Option (Borrow n)`.
* `IsBorrowing n K C d s b`: conditions (b1) to (b6) for `(s, b.t, b.q, b.r, b.m)` and the gate
  `b.gate` of `C`, against nested data `d`.
* `BorrowedTermOK n C d s b`: the gate at `bw s` has role `B` of `s` and is
  `AND(a, root of O_s)` in either order, `a` the wire `n + b.gate`.
* `BValid n K A C d`: `d` labels `C` as a borrowed cover circuit of `(K, A)`.
* `NoBorrowing d`: no vertex carries a borrowing.
* `IsBorrowedCoverCircuit n K A C`: some `d` with `BValid`.

Caveats a statement must respect.
* All caveats of `NestedCoverCircuit` hold here (`A` disjoint from the edge vertices, the empty
  case, `ReadsBack` imposing acyclicity, vertex numbers in `role` compared with `t.val`).
* The note works under (G1) no triangle and no 4-cycle and (G2) no cycle inside a minimum cover.
  Nothing here enforces them. The consequences the note draws from them (`q` outside the cover,
  two borrowings never share `t`, the borrowed gate list is acyclic, the circuit computes
  `F_(K,A)` with `|A| + |E| + |T| - 1` gates) are theorems of the note on paper, not part of the
  definition; `q` outside the cover in particular is NOT required.
* "Distinct" is `[s, t, q, r, m].Nodup`; `m != t` is part of it.
* The degenerate case of the note (`t` owns only `s`) is NOT a borrowing here ((b2) asks for the
  two owned vertices `s` and `q`, with `q != s` by distinctness).
* `IsBorrowedCoverCircuit` includes the nested ones. A statement about the circuits that are
  borrowed and not nested must say so (for example
  `IsBorrowedCoverCircuit n K A C ∧ ¬ IsNestedCoverCircuit n K A C`).
-/

namespace PEqualNP.MetaComplexity.BorrowedCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- One borrowing `(s, t, q, r, m)` with the gate `a` of `O_m`; the vertex `s` is the key under
which it is stored in `BCCData`. -/
structure Borrow (n : ℕ) where
  /-- The receiver `t`: `s -> t`, and `t` owns exactly `s` and `q`. -/
  t : Fin n
  /-- The other vertex `q` owned by `t`. -/
  q : Fin n
  /-- The borrowed vertex `r`, owned by `m` and adjacent to `q`. -/
  r : Fin n
  /-- The cover vertex `m` (called `n` in the note) owning `ms` and `mr`. -/
  m : Fin n
  /-- The gate number of `a = OR(lam_m(s), lam_m(r))`, a gate of `O_m`; its wire is
  `n + gate`. -/
  gate : ℕ
  deriving DecidableEq

/-- The data of a borrowed cover circuit: nested data and, for each `s`, an optional
borrowing. -/
structure BCCData (n : ℕ) where
  /-- The nested data underneath. -/
  base : NCCData n
  /-- `borrow s = some b`: the term of `s` is borrowed, along `(s, b.t, b.q, b.r, b.m)`. -/
  borrow : Fin n → Option (Borrow n)

/-- Conditions (b1) to (b6): `(s, b.t, b.q, b.r, b.m)` with the gate `b.gate` of `C` is a
borrowing in the nested data `d`. -/
def IsBorrowing (n : ℕ) (K : SimpleGraph (Fin n)) (C : Circuit) (d : NCCData n) (s : Fin n)
    (b : Borrow n) : Prop :=
  [s, b.t, b.q, b.r, b.m].Nodup ∧
    -- (b1)
    d.tie s = some b.t ∧
    -- (b2)
    b.t ∈ d.cover ∧ d.tie b.t = none ∧ (∀ v, d.owns b.t v = true ↔ (v = s ∨ v = b.q)) ∧
    -- (b3)
    b.m ∈ d.cover ∧ d.owns b.m s = true ∧ d.owns b.m b.r = true ∧
    -- (b4)
    K.Adj b.r b.q ∧
    -- (b5)
    d.lam b.m s = d.zroot s ∧ b.gate < C.gates.length ∧ d.role b.gate = (Kind.o, b.m.val) ∧
    (gateAt C b.gate).op = GateOp.or ∧
    ((gateAt C b.gate).inputs = [d.lam b.m s, d.lam b.m b.r] ∨
      (gateAt C b.gate).inputs = [d.lam b.m b.r, d.lam b.m s]) ∧
    -- (b6)
    ∀ t', d.owns t' b.t = true → d.lam t' b.t = b.t.val

/-- The borrowed term of `s`: the gate at wire `bw s` has role `B` of `s` and is the AND of the
wire of `a` (wire `n + b.gate`) and the root of `O_s`, in either order. -/
def BorrowedTermOK (n : ℕ) (C : Circuit) (d : NCCData n) (s : Fin n) (b : Borrow n) : Prop :=
  ∃ j < C.gates.length, d.bw s = n + j ∧ d.role j = (Kind.b, s.val) ∧
    (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [n + b.gate, d.oroot s] ∨ (gateAt C j).inputs = [d.oroot s, n + b.gate])

/-- The data `d` labels `C` as a borrowed cover circuit of `(K, A)`: `Valid` of the nested
module on `d.base`, with the term condition of each borrowed `s` replaced by `BorrowedTermOK`,
and every recorded borrowing satisfying `IsBorrowing`. -/
def BValid (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit)
    (d : BCCData n) : Prop :=
  ReadsBack n C ∧ IsMinCover K d.base.cover ∧ OwnerOK K d.base ∧ TieOK d.base ∧
    RolesOK n C d.base ∧
    (∀ t ∈ d.base.cover,
      ((d.borrow t).isNone = true → TermOK n C d.base t) ∧
      (∀ b ∈ d.borrow t, BorrowedTermOK n C d.base t b) ∧
      IsOrTree n C (gatesOf d.base C Kind.z t.val) (zLeaves d.base t) (d.base.zroot t) ∧
      IsOrTree n C (gatesOf d.base C Kind.o t.val) (oLeaves d.base t) (d.base.oroot t) ∧
      ∀ r, d.base.owns t r = true → LamOK n C d.base t r) ∧
    IsOrTree n C (topGates d.base C) (topLeaves d.base A) C.output ∧
    ∀ s, ∀ b ∈ d.borrow s, IsBorrowing n K C d.base s b

/-- No vertex carries a borrowing. -/
def NoBorrowing {n : ℕ} (d : BCCData n) : Prop :=
  ∀ s, d.borrow s = none

/-- `C` is a borrowed cover circuit of `(K, A)` on `n` inputs (section 2 of the note). Nested
cover circuits are the case with no borrowing. -/
def IsBorrowedCoverCircuit (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (C : Circuit) : Prop :=
  ∃ d : BCCData n, BValid n K A C d

/-! ## Decidability, so that small rows can be checked by `decide` -/

attribute [local instance] gateOpDecEq

instance (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (C : Circuit) (d : NCCData n)
    (s : Fin n) (b : Borrow n) : Decidable (IsBorrowing n K C d s b) := by
  unfold IsBorrowing; infer_instance

instance (n : ℕ) (C : Circuit) (d : NCCData n) (s : Fin n) (b : Borrow n) :
    Decidable (BorrowedTermOK n C d s b) := by
  unfold BorrowedTermOK; infer_instance

instance (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (C : Circuit) (d : BCCData n) : Decidable (BValid n K A C d) := by
  unfold BValid; infer_instance

end PEqualNP.MetaComplexity.BorrowedCover

end BorrowedCoverCircuit

section DeMorganFormula

/-!
# De Morgan formulas and leaf size

A de Morgan formula on `n` inputs is a binary tree whose inner nodes are AND or OR and whose
leaves are literals: an input or the negation of an input. Negations sit only at the leaves and
cost nothing; there are no constants, so every formula has at least one leaf. The leaf size is
the number of leaves, counting every occurrence of a literal. This is the usual formula size
measure over the de Morgan basis.

It differs from the circuit size of `Defs/MetaComplexity.lean` in two ways: nothing is shared
(a subformula used twice is written twice), and negations are free.

* `DMFormula n`: the formulas. `DMFormula.eval φ x`: the value at the input `x`.
* `DMFormula.leaves φ`: the number of leaves.
* `HasLeafSize n f s`: some formula with at most `s` leaves computes `f`.
-/

namespace PEqualNP.MetaComplexity

/-- A de Morgan formula on `n` inputs: a literal `lit i b` (the input `i` when `b` is true, its
negation when `b` is false), or the AND or the OR of two formulas. -/
inductive DMFormula (n : ℕ) : Type
  | lit : Fin n → Bool → DMFormula n
  | and : DMFormula n → DMFormula n → DMFormula n
  | or : DMFormula n → DMFormula n → DMFormula n

/-- The value of a formula at the input `x`. -/
def DMFormula.eval {n : ℕ} : DMFormula n → (Fin n → Bool) → Bool
  | DMFormula.lit i b, x => if b then x i else !x i
  | DMFormula.and φ ψ, x => φ.eval x && ψ.eval x
  | DMFormula.or φ ψ, x => φ.eval x || ψ.eval x

/-- The number of leaves of a formula, every occurrence of a literal counted. -/
def DMFormula.leaves {n : ℕ} : DMFormula n → ℕ
  | DMFormula.lit _ _ => 1
  | DMFormula.and φ ψ => φ.leaves + ψ.leaves
  | DMFormula.or φ ψ => φ.leaves + ψ.leaves

/-- `f` is computed by a de Morgan formula with at most `s` leaves. -/
def HasLeafSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ φ : DMFormula n, φ.leaves ≤ s ∧ ∀ x : Fin n → Bool, φ.eval x = f x

end PEqualNP.MetaComplexity

end DeMorganFormula

section InvisibleWire

/-!
# Invisible wires of a circuit

A semantic label on the wires of a root circuit (`PEqualNP.CircuitLowerBounds.Circuit`) on `n`
inputs. An input `x : Fin n → Bool` is LIGHT when at most one of its bits is true (weight 0 or
1). A wire is INVISIBLE when its value is `false` on every light input. The invisible count of a
circuit is its number of invisible gate wires.

Examples: the AND of two distinct inputs; any wire below `(x1 OR x3) AND (x2 OR x6)` on the
light inputs. Non-examples: any input wire (true at its own single input); any OR of a
nonempty set of inputs (true at a single input of the set).

Names:
* `IsLight n x`: at most one bit of `x : Fin n → Bool` is true.
* `IsInvisible C n w`: wire `w` of `C` reads `false` on every light input. Decidable.
* `invisibleCount C n`: the number of `j < C.gates.length` such that the gate wire `n + j` is
  invisible.
* `wireValue C n x w` is reused from `Defs/BlindGate.lean`.

Caveats a statement must respect:
* The wire index `w` counts the inputs first: wires `0 .. n - 1` are the inputs, gate `j` is
  wire `n + j`. The number of inputs `n` is an argument and must be the same `n` as in
  `Circuit.Decides` or `NotPremium.Computes`.
* A wire index that does not exist reads `false` (as `wireValue` does), so a MISSING wire is
  invisible. `invisibleCount` counts only existing gate wires, so it is not affected; a
  statement about `IsInvisible C n w` for an arbitrary `w` must say `w` exists if that matters.
* A constant `false` gate (for instance `OR []`) is invisible; a constant `true` gate is not.
* The notion is SEMANTIC and any gate operation is allowed, NOT, MOD and MAJORITY included: it
  looks only at the wire's values on the `n + 1` light inputs, not at how the wire is built.
* When `n = 0` the only input is the empty one, which is light.
* Counts (`shadowCount`, `invisibleCount`) include gates no output depends on, so "at least `k`
  such gates" can be met by padding a circuit: speak of least circuits, or count only gates an
  output depends on.
-/

namespace PEqualNP.InvisibleWire

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate

/-- At most one bit of `x` is true (weight 0 or 1). -/
def IsLight (n : ℕ) (x : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => x i = true).card ≤ 1

instance (n : ℕ) (x : Fin n → Bool) : Decidable (IsLight n x) := by
  unfold IsLight; infer_instance

/-- Wire `w` of `C` on `n` inputs is invisible: it reads `false` on every light input. A wire
that does not exist reads `false`, so it is invisible. -/
def IsInvisible (C : Circuit) (n w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, IsLight n x → wireValue C n x w = false

instance (C : Circuit) (n w : ℕ) : Decidable (IsInvisible C n w) := by
  unfold IsInvisible; infer_instance

/-- The number of gates of `C` on `n` inputs whose wire (`n + j` for gate `j`) is invisible. -/
def invisibleCount (C : Circuit) (n : ℕ) : ℕ :=
  ((List.range C.gates.length).filter fun j => decide (IsInvisible C n (n + j))).length

end PEqualNP.InvisibleWire

end InvisibleWire

section NotBracket

/-!
# NOT brackets of a family of monotone outputs, and the bracket cost

A family of `m` monotone Boolean functions on `n` inputs, `f : Fin m → ((Fin n → Bool) → Bool)`
(for a Boolean sum, output `i` is the OR of the inputs in set `i`), has a NOT bracket `(G, h)`
when:

* `h : (Fin n → Bool) → Bool` is ONE monotone function of the `n` inputs, shared by all outputs;
* `G : Fin m → ((Fin (n + 1) → Bool) → Bool)` gives `m` functions of `(x, z)`, each monotone in
  all `n + 1` arguments, with the extra input `z` LAST (position `n`, written `Fin.snoc x z`);
* `G i (x, NOT h x) = f i x` for every output `i` and every `x`.

Plugging `NOT h` into the `z` input costs one NOT gate, so a bracket is a multi-output circuit
for `f` with exactly one NOT gate, cut open at that gate.

The bracket cost counts `G` and `h` together, as ONE list of gates on the root circuit model
(`PEqualNP.CircuitLowerBounds.Circuit`) with `m + 1` marked wires:

* the list reads `n + 1` input wires: wires `0` to `n - 1` carry `x`, wire `n` carries `z`;
* every gate is an AND or an OR (`IsMonotoneCircuit`) reading at most two wires;
* wire `oG i` carries `G i`, for each output `i`: any existing wire (input, `z` or gate);
* wire `oh` carries `h`: any existing wire that does NOT depend on `z` syntactically
  (`zReach`): an input of `x`, or a gate none of whose ancestors is wire `n`. So the trivial
  bracket `G i (x, z) = f i x`, `h = x 0` costs the plain monotone size of `f`;
* gates are shared freely between the outputs and `h`, and each gate is counted once.

Names:
* `withZ x z`: the point `(x, z)` on `n + 1` inputs, `z` last (`Fin.snoc x z`).
* `IsNotBracket n m f G h`: every `f i`, every `G i` and `h` are monotone, and
  `G i (withZ x (!h x)) = f i x` for all `i` and `x`.
* `wireValue C y o`: the value of wire `o` of `C` on input `y` (`false` if there is none).
* `zReach n C`: for each wire of `C` on `n + 1` inputs, whether it depends syntactically on wire
  `n` (the wire `n` itself does; a gate does when some wire it reads does).
* `IsBracketCircuit n C oG oh`: `C` is a NOT-free fan-in-two list on `n + 1` inputs, every `oG i`
  is an existing wire, and `oh` is an existing wire that does not depend on `z`.
* `ComputesBracket n C oG oh G h`: on every `(x, z)`, wire `oG i` carries `G i (x, z)` for every
  `i`, and wire `oh` carries `h x`.
* `HasBracketCost n m f s`: some bracket of `f` is computed together by such a list of at most
  `s` gates.
* `bracketCost n m f`: the least such `s` (`sInf`; it is `0` if no `s` exists, which happens
  only when some `f i` is not monotone).
* `notCount C`: the number of NOT gates of `C`.
* `HasOneNotCost n m f s`: some list of AND, OR, NOT gates of fan-in at most two, with EXACTLY
  one NOT gate (it may read an input wire) and at most `s` gates, has one existing wire per
  output `i` carrying `f i` on every input of length `n`.
* `OneNotSizeIdentity n m f`: the thinker's identity, as a CANDIDATE statement only (not proved,
  not a theorem of this file): for monotone `f`, `HasOneNotCost n m f (s + 1) ↔
  HasBracketCost n m f s` for every `s`.
* `booleanSum n m S`: the Boolean sum of the sets `S i ⊆ Fin n`: output `i` is the OR of the
  inputs in `S i` (the OR of an empty set is `false`).

Caveats a statement must respect:
* Monotonicity of every `f i` is part of `IsNotBracket`. Without it `G (x, NOT h x)` need not be
  monotone (for instance `G = z`, `h = x 0` gives `NOT x 0`).
* `h` is independent of `z` SYNTACTICALLY (no path from wire `n` to wire `oh`), which is what
  lets the NOT gate be inserted without a cycle. A wire whose value happens not to depend on `z`
  but which reads `z` does not qualify.
* The circuit is the root model: a wire index that does not exist yet reads `false`, an AND
  reading no wire is the constant `true`, an OR reading no wire the constant `false`. Every gate
  counts, constant gates and copies included; inputs are not counted. The `output` field of the
  `Circuit` is ignored here: the marked wires are `oG` and `oh`.
* Several outputs may share one wire (`oG` need not be injective); `oh` may equal some `oG i`.
* `HasOneNotCost` counts EXACTLY one NOT gate. With "at most one", a NOT-free circuit would
  count. Its degenerate cases (a NOT reading a wire that does not exist, or reading nothing) are
  not excluded; the identity is a candidate, and a statement assumes what it needs.
* Fan-in two is built in, for `G` and `h` alike.
* Inputs in the thinker's text are numbered from `1`; here they are numbered from `0`, so the
  sum `{123, 14, 24, 34}` is `booleanSum 4 4 ![{0,1,2}, {0,3}, {1,3}, {2,3}]`.
-/

namespace PEqualNP.NotBracket

open PEqualNP.CircuitLowerBounds

attribute [local instance] lineDegreeGateOpDecEq

/-- The point `(x, z)` on `n + 1` inputs: `x` first, the extra input `z` last (position `n`). -/
def withZ {n : ℕ} (x : Fin n → Bool) (z : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc x z

/-- `(G, h)` is a NOT bracket of the family `f` of `m` monotone functions on `n` inputs: every
`f i`, every `G i` and `h` are monotone, `G i` reads `(x, z)` with `z` last, and
`G i (x, NOT h x) = f i x` for every `i` and `x`. One `h` serves all outputs. -/
def IsNotBracket (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool)
    (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool) : Prop :=
  (∀ i, Monotone (f i)) ∧ (∀ i, Monotone (G i)) ∧ Monotone h ∧
    ∀ (i : Fin m) (x : Fin n → Bool), G i (withZ x (!h x)) = f i x

/-- The value of wire `o` of `C` on input `y` (`false` if the wire does not exist). -/
def wireValue (C : Circuit) (y : List Bool) (o : ℕ) : Bool :=
  (C.wires y).getD o false

/-- For each wire of `C` on `n + 1` inputs, in the order of `Circuit.wires`: whether it depends
syntactically on the input wire `n` (the `z` wire). Input wires below `n` do not, wire `n` does,
and a gate does exactly when some wire it reads does (a wire that does not exist does not). -/
def zReach (n : ℕ) (C : Circuit) : List Bool :=
  C.gates.foldl (fun d g => d ++ [g.inputs.any fun i => d.getD i false])
    (List.replicate n false ++ [true])

/-- `C` is a list for a bracket on `n` inputs with `m` outputs: AND and OR gates of fan-in at
most two, on `n + 1` input wires (wire `n` is `z`); every output wire `oG i` exists; the wire
`oh` of `h` exists and does not depend on `z`. -/
def IsBracketCircuit (n : ℕ) {m : ℕ} (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ) : Prop :=
  IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    (∀ i, oG i < n + 1 + C.size) ∧ oh < n + 1 + C.size ∧ (zReach n C).getD oh true = false

/-- On every `(x, z)`, wire `oG i` of `C` carries `G i (x, z)` for every `i`, and wire `oh`
carries `h x`. The input list is `x` then `z`. -/
def ComputesBracket (n : ℕ) {m : ℕ} (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ)
    (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ (x : Fin n → Bool) (z : Bool),
    (∀ i, wireValue C (List.ofFn x ++ [z]) (oG i) = G i (withZ x z)) ∧
      wireValue C (List.ofFn x ++ [z]) oh = h x

/-- Bracket cost at most `s`: some NOT bracket `(G, h)` of `f` is computed together by one
NOT-free fan-in-two list of at most `s` gates, as in `IsBracketCircuit` and `ComputesBracket`. -/
def HasBracketCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool),
    IsNotBracket n m f G h ∧
      ∃ (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ),
        IsBracketCircuit n C oG oh ∧ C.size ≤ s ∧ ComputesBracket n C oG oh G h

/-- The bracket cost `br f`: the least `s` with `HasBracketCost n m f s` (`0` if none). -/
noncomputable def bracketCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) : ℕ :=
  sInf {s | HasBracketCost n m f s}

/-- The number of NOT gates of `C`. -/
def notCount (C : Circuit) : ℕ :=
  (C.gates.filter fun g => decide (g.op = GateOp.not)).length

/-- Some list of AND, OR and NOT gates of fan-in at most two, with exactly one NOT gate and at
most `s` gates, has for each output `i` an existing wire carrying `f i` on `n` inputs. -/
def HasOneNotCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (C : Circuit) (oF : Fin m → ℕ),
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) ∧
    notCount C = 1 ∧ C.size ≤ s ∧ (∀ i, oF i < n + C.size) ∧
      ∀ (i : Fin m) (x : Fin n → Bool), wireValue C (List.ofFn x) (oF i) = f i x

/-- The thinker's size identity, as a CANDIDATE statement only: for a family of monotone
outputs, the least list with exactly one NOT gate has one gate more than the bracket cost. -/
def OneNotSizeIdentity (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) : Prop :=
  (∀ i, Monotone (f i)) → ∀ s : ℕ, HasOneNotCost n m f (s + 1) ↔ HasBracketCost n m f s

/-- The Boolean sum of the sets `S i`: output `i` is the OR of the inputs in `S i`. -/
def booleanSum (n m : ℕ) (S : Fin m → Finset (Fin n)) : Fin m → (Fin n → Bool) → Bool :=
  fun i x => decide (∃ j ∈ S i, x j = true)

end PEqualNP.NotBracket

end NotBracket

section NotPremium

/-!
# The NOT premium of a family of Boolean functions

Built on the root circuits of `Defs/CircuitLowerBounds` (`Gate`, `Circuit`, `Circuit.eval`),
with the encoding the one-NOT rows use: a list of gates `gates`, one output wire `out w` per
member `w` of the family, every gate an AND, OR or NOT reading at most two wires, every gate
counted, and "at most one NOT gate" as a map `Fin 1 → Fin gates.length` hitting every NOT
position.

For a family `F = (F 0, .., F (m - 1))` of functions on `n` inputs:

* the PLAIN size is the least number of gates of a NOT-free list (AND and OR, at most two
  wires each) computing all of `F` at once;
* a NOT gate at position `q` of a list is ESSENTIAL if replacing that gate by the constant
  `false`, and also by the constant `true`, each changes the value of some output wire on some
  input (both replacements must change something, not just one of them);
* the ONE-NOT size is the least number of gates of a list computing `F` with exactly one NOT
  gate, that gate essential;
* the NOT PREMIUM is the one-NOT size minus the plain size, an integer, or `⊤` when either
  size does not exist.

Names.
* `Basis2 gates`: every gate is AND, OR or NOT and reads at most two wires.
* `MonoBasis2 gates`: every gate is AND or OR and reads at most two wires.
* `Computes n gates out F`: output wire `out w` computes `F w`, for every `w` and every input.
* `orFamily S`: the family of ORs of the sets `S w` (the line-ORs of the rows).
* `constGate b`: the gate with no inputs and constant value `b` (`AND []` is `true`,
  `OR []` is `false`, as on the root).
* `replaceByConst gates q b`: the list with position `q` replaced by `constGate b`.
* `ChangesSomeOutput n gates gates' out`: some output wire differs between the two lists on
  some input.
* `EssentialNot n gates out q`: the gate at `q` is a NOT gate and both constant replacements
  change some output.
* `AtMostOneNot gates`: the row encoding, a map from `Fin 1` covering every NOT position.
* `EssentialOneNot n gates out`: at most one NOT gate and an essential NOT gate exists, that is
  exactly one NOT gate and it is essential.
* `plainSize n F : ℕ∞` (the thinker's `J_0`) and `oneNotSize n F : ℕ∞` (`J_{=1}`), as `sInf`
  of the attained sizes (`⊤` when none).
* `notPremium n F : WithTop ℤ`, `oneNotSize - plainSize` when both are finite, else `⊤`.

Caveats for statements.
* The value `⊤` is real, not a junk value: the constant `false` family has no list with an
  essential NOT gate (an output after a single NOT is monotone in the NOT wire, so replacing
  by `false` cannot change a constant `false` output), and a non-monotone `F` has no plain
  list. The thinker's notion is for monotone `F`; state monotonicity where it is used.
* `⊤` also arises for monotone, non-constant families (on paper): on one
  input, `F = x0` has no list with one essential NOT gate. So "the premium is at least `c`" can
  hold for that trivial reason; a statement of that form must also assert that the one-NOT size
  is finite, or be worded as "every list with one essential NOT gate has at least .. gates".
* Wire indices that do not exist read `false`, and a gate may have zero or one input (a
  constant or a copy), as on the root and in the rows: such gates are allowed and counted.
* "Changes some output" compares the replaced list with the original list. Under `Computes`
  the original values are `F`, so this is the thinker's "changes some output of F".
* The replaced gate is the constant itself (a gate with no inputs), so the replaced list has
  the same length and every later wire keeps its index.
* Plain size uses `MonoBasis2` (no NOT gate at all). The one-NOT size counts the NOT gate.
* `notPremium` is in `WithTop ℤ`; the premium is negative exactly when one essential NOT gate
  saves gates.
-/

namespace PEqualNP.NotPremium

open PEqualNP.CircuitLowerBounds

/-- Every gate is an AND, OR or NOT gate reading at most two wires. -/
def Basis2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

/-- Every gate is an AND or OR gate reading at most two wires (no NOT gate). -/
def MonoBasis2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- The list `gates` with output wires `out` computes the family `F` on `n` inputs. -/
def Computes {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (F : Fin m → (Fin n → Bool) → Bool) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = F w x

/-- The family of ORs of the sets `S w`, as in the line-OR rows. -/
def orFamily {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fin m → (Fin n → Bool) → Bool :=
  fun w x => decide (∃ v ∈ S w, x v = true)

/-- The constant gate of value `b`: no inputs, AND (value `true`) or OR (value `false`). -/
def constGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

/-- The list with the gate at position `q` replaced by the constant `b`. -/
def replaceByConst (gates : List Gate) (q : ℕ) (b : Bool) : List Gate :=
  gates.set q (constGate b)

/-- Some output wire takes a different value in `gates'` than in `gates` on some input. -/
def ChangesSomeOutput {m : ℕ} (n : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ) : Prop :=
  ∃ (w : Fin m) (x : Fin n → Bool),
    Circuit.eval ⟨gates', out w⟩ (List.ofFn x) ≠ Circuit.eval ⟨gates, out w⟩ (List.ofFn x)

/-- The gate at position `q` is an ESSENTIAL NOT gate: it is a NOT gate, and replacing it by
the constant `false` changes some output, and replacing it by the constant `true` also changes
some output. -/
def EssentialNot {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (q : Fin gates.length) : Prop :=
  (gates.get q).op = GateOp.not ∧
    ChangesSomeOutput n gates (replaceByConst gates q.val false) out ∧
    ChangesSomeOutput n gates (replaceByConst gates q.val true) out

/-- At most one NOT gate, in the row encoding: a map from `Fin 1` covering every NOT
position. -/
def AtMostOneNot (gates : List Gate) : Prop :=
  ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i

/-- Exactly one NOT gate, and it is essential. -/
def EssentialOneNot {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  AtMostOneNot gates ∧ ∃ q : Fin gates.length, EssentialNot n gates out q

/-- The plain size `J_0`: the least number of gates of a NOT-free list computing `F`
(`⊤` if there is none). -/
noncomputable def plainSize {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ (gates : List Gate) (out : Fin m → ℕ),
    MonoBasis2 gates ∧ Computes n gates out F ∧ (gates.length : ℕ∞) = s}

/-- The one-NOT size `J_{=1}`: the least number of gates of a list computing `F` with exactly
one NOT gate, that gate essential (`⊤` if there is none). -/
noncomputable def oneNotSize {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ (gates : List Gate) (out : Fin m → ℕ),
    Basis2 gates ∧ EssentialOneNot n gates out ∧ Computes n gates out F ∧
      (gates.length : ℕ∞) = s}

/-- The NOT premium `pi(F) = J_{=1}(F) - J_0(F)`, an integer when both sizes are finite,
`⊤` otherwise. -/
noncomputable def notPremium {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) :
    WithTop ℤ :=
  if oneNotSize n F = ⊤ ∨ plainSize n F = ⊤ then ⊤
  else (((oneNotSize n F).toNat : ℤ) - ((plainSize n F).toNat : ℤ) : ℤ)

end PEqualNP.NotPremium

end NotPremium

section SharedOr

/-!
# True users of a gate and shared OR gates of an AND/OR list on a plane

A new notion, defined here.

The setting. A plane (projective or not) is data, as in `PEqualNP.Defs.PencilGate`: `n` points
`Fin n` and `m` lines, a family `S : Fin m → Finset (Fin n)` of point sets. A list of gates is a
root circuit `C` (`PEqualNP.CircuitLowerBounds.Circuit`) on `n` inputs, input `i` being the point
`i`, with one OUTPUT WIRE per line given by a map `out : Fin m → ℕ` (the wire meant to compute the
AND of the points of `S l`). The field `C.output` plays no part. A gate is named by its WIRE index
`w`, as in the netlists on file: wires `0 .. n - 1` are the inputs, gate number `j` is wire `n + j`.

* The CONE of the output of line `l` is the set of wires `w` with `w = out l`, or `w` and `out l`
  both gate wires and gate `w - n` strictly inside the cone of gate `out l - n` in the sense of
  `PEqualNP.EdgeOwnership.InCone` (the gate reads it, directly or through a chain of gates). The
  cone CONTAINS the output wire itself (the thinker's `Conj(g)` contains the output, so `o_l` is a
  true user of itself).
* The TRUE USERS of wire `w`: the lines `l` such that `w` is in the cone of `out l` AND `w` is true
  on the light input `lineInput S l` (true exactly at the points of `S l`).
* A SHARED OR gate: a gate wire `w` (`n ≤ w < n + C.gates.length`) whose gate is an OR gate and
  whose true users are NOT CONCURRENT: no point lies on every line of them.

Names:
* `InOutCone n C w v`: wire `w` is in the cone of wire `v` (reflexive).
* `IsTrueUser S C out w l`, `trueUsers S C out w : Finset (Fin m)`.
* `IsConcurrent S U`: some point lies on every line of `U : Finset (Fin m)`.
* `IsOrWire n C w`: `w` is a gate wire whose gate is an OR gate.
* `IsSharedOr S C out w`: `IsOrWire n C w` and the true users of `w` are not concurrent.
* `HasSharedOr S C out`: some gate wire of `C` is a shared OR gate.
* `sharedOrCount S C out`: the number of gates of `C` that are shared OR gates.

Caveats a statement must respect:
* NO TRUE USERS IS NOT SHARED. An empty set of lines is concurrent whenever `n ≥ 1` (every point
  lies on all of its lines), and a single line is concurrent when it has a point; so with `n ≥ 1`
  a shared OR gate has at least two true users, and in a projective plane (two lines meet) at least
  three. This is the thinker's reading: "SH gate: an OR gate g with U(g) not concurrent (no point
  on every line of U(g))", and "in a projective plane two lines always meet, so an SH gate has at
  least three true users" (column-sharing.md, sections 0 and 2.1). A gate no output uses is a dead
  gate, not a shared one. Degenerate: with `n = 0` (no points) every OR gate is shared.
* Wire indices, not gate indices. `IsSharedOr` holds only for gate wires; an input wire is never an
  OR gate. Inside `HasSharedOr` and `sharedOrCount` the gates are `n + j`, `j < C.gates.length`.
* The cone of an input wire is that wire alone: if `out l` is an input wire (a projection) only
  that wire is in its cone. An input wire below a gate is not counted in the cone (`InCone` is on
  gates); this does not matter for OR gates, which are gate wires.
* `InCone` sees only wires a gate really reads: a wire index at or past the gate's own wire reads
  `false` in the root model and is not in its cone.
* The notion is SEMANTIC only on the `m` light inputs `lineInput S l`; a gate's values elsewhere
  play no part. It does not assume that `C` computes the line-ANDs, that it is monotone, of fan-in
  two, or that `S` is a projective plane: state those as hypotheses.
* `out` need not be injective, and an output wire past the end of the list reads `false` and has
  only itself in its cone (so it has no true users).
-/

namespace PEqualNP.SharedOr

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

/-- Wire `w` is in the (reflexive) cone of wire `v`: `w = v`, or both are gate wires and gate
`w - n` lies strictly inside the cone of gate `v - n`. -/
def InOutCone (n : ℕ) (C : Circuit) (w v : ℕ) : Prop :=
  w = v ∨ (n ≤ w ∧ n ≤ v ∧ InCone n C (w - n) (v - n))

instance (n : ℕ) (C : Circuit) (w v : ℕ) : Decidable (InOutCone n C w v) := by
  unfold InOutCone; infer_instance

/-- Line `l` is a TRUE USER of wire `w`: `w` is in the cone of the output wire `out l`, and `w` is
true on the input whose true points are exactly those of `S l`. -/
def IsTrueUser {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ)
    (l : Fin m) : Prop :=
  InOutCone n C w (out l) ∧ wireValue C (lineInput S l) w = true

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ)
    (l : Fin m) : Decidable (IsTrueUser S C out w l) := by
  unfold IsTrueUser; infer_instance

/-- The TRUE USERS of wire `w`. -/
def trueUsers {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Finset (Fin m) :=
  Finset.univ.filter fun l => IsTrueUser S C out w l

/-- The lines of `U` are CONCURRENT: some point lies on every one of them (true for `U = ∅` when
there is a point). -/
def IsConcurrent {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin m)) : Prop :=
  ∃ p : Fin n, ∀ l ∈ U, p ∈ S l

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin m)) :
    Decidable (IsConcurrent S U) := by
  unfold IsConcurrent; infer_instance

/-- Wire `w` is a gate wire of `C` (on `n` inputs) whose gate is an OR gate. -/
def IsOrWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or

instance (n : ℕ) (C : Circuit) (w : ℕ) : Decidable (IsOrWire n C w) := by
  unfold IsOrWire; infer_instance

/-- Wire `w` is a SHARED OR gate: an OR gate whose true users have no common point. -/
def IsSharedOr {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Prop :=
  IsOrWire n C w ∧ ¬ IsConcurrent S (trueUsers S C out w)

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Decidable (IsSharedOr S C out w) := by
  unfold IsSharedOr; infer_instance

/-- Some gate of `C` (wire `n + j`, `j < C.gates.length`) is a shared OR gate. -/
def HasSharedOr {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) : Prop :=
  ∃ j < C.gates.length, IsSharedOr S C out (n + j)

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) :
    Decidable (HasSharedOr S C out) := by
  unfold HasSharedOr; infer_instance

/-- The number of gates of `C` (wires `n` to `n + C.gates.length - 1`) that are shared OR
gates. -/
def sharedOrCount {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) : ℕ :=
  ((Finset.range C.gates.length).filter fun j => IsSharedOr S C out (n + j)).card

end PEqualNP.SharedOr

end SharedOr

section SharingOrder

/-!
# The sharing order of a family of outputs

A family `F : Fin m → (Fin n → Bool) → Bool` of `m` Boolean functions on `n` inputs, and a
domain `D : Set (Fin n → Bool)` of inputs on which circuits must be right. Circuits are root
circuits (`PEqualNP.CircuitLowerBounds.Circuit`) of AND and OR gates (`IsMonotoneCircuit`), each
gate reading at most two wires, with no NOT; every gate counts in the size.

* The JOINT least size of a subfamily `I : Finset (Fin m)` is the least number of gates of one
  such circuit with, for each `i ∈ I`, a chosen wire (an input wire or a gate wire) that agrees
  with `F i` on every input of `D`. It is `⊤` when no such circuit exists (for instance when some
  `F i` is not monotone on `D`).
* The single least size of output `i` is the joint least size of `{i}`.
* The SHARING ORDER is the least `k` such that some subfamily of `k` outputs has joint least size
  strictly below the sum of the single least sizes of its members; `⊤` if no subfamily saves.

Names:
* `IsMonoFanInTwo C`: every gate of `C` is AND or OR and reads at most two wires.
* `Circuit.wireOn C x j`: the value of wire `j` of `C` on the input `x : Fin n → Bool`.
* `JointComputes D F I C out`: wire `out i` of `C` agrees with `F i` on `D`, for each `i ∈ I`.
* `JointSizeAtMost D F I s`: some `IsMonoFanInTwo` circuit with at most `s` gates jointly
  computes `F` on `I` over `D`.
* `jointSize D F I : ℕ∞`: the joint least size.
* `singleSize D F i : ℕ∞`: `jointSize D F {i}`.
* `Saves D F I`: `jointSize D F I < ∑ i ∈ I, singleSize D F i`.
* `sharingOrder D F : ℕ∞`: the least card of a saving subfamily, `⊤` if none.
* Helpers for rows: `andOf S` (the AND of the inputs in `S`, `true` on `S = ∅`) and
  `weightBand n a b` (the inputs with between `a` and `b` true bits, both ends included).

Caveats a statement must respect:
* The field `Circuit.output` plays no part: the outputs are the wires `out i`. An output wire may
  be an input wire (size `0` for a projection) and may be shared by several outputs.
* A wire index that does not exist reads `false` (root convention), so the constant `false` costs
  no gate; the constant `true` costs one gate (an AND reading no wire).
* Fan-in two (and zero or one) is built in; a gate with fan-in one copies its wire.
* The domain matters: on a partial `D` a function can be cheaper, and a function that is not
  monotone can still have a monotone circuit right on `D`.
* Subfamilies of size `0` and `1` never save, so `sharingOrder` is `⊤` or at least `2`.
* The sum is in `ℕ∞`: if some single size is `⊤` then so is the joint size, and that subfamily
  does not save.
* Unused gates count; the least size never uses them.
* Degenerate families: two outputs that agree on `D`, or an output constant on `D`, can make the
  order `2` for a trivial reason. A statement about the sharing order of a family
  should carry the hypothesis "outputs pairwise different and not constant on `D`".
-/

namespace PEqualNP.CircuitLowerBounds

open Finset

/-- Every gate of `C` is an AND or an OR gate reading at most two wires. -/
def IsMonoFanInTwo (C : Circuit) : Prop :=
  IsMonotoneCircuit C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

/-- The value of wire `j` of `C` on the input `x` (`false` if the wire does not exist). -/
def Circuit.wireOn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD j false

/-- For each `i ∈ I`, the wire `out i` of `C` agrees with `F i` on every input of `D`. -/
def JointComputes {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) (C : Circuit) (out : Fin m → ℕ) : Prop :=
  ∀ i ∈ I, ∀ x ∈ D, C.wireOn x (out i) = F i x

/-- Some AND/OR circuit of fan-in at most two with at most `s` gates computes every `F i`,
`i ∈ I`, on `D`, each on a wire of its own choice. -/
def JointSizeAtMost {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) (s : ℕ) : Prop :=
  ∃ C : Circuit, ∃ out : Fin m → ℕ, IsMonoFanInTwo C ∧ C.size ≤ s ∧ JointComputes D F I C out

/-- The joint least size of the subfamily `I` on `D` (`⊤` if no circuit exists). -/
noncomputable def jointSize {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) (I : Finset (Fin m)) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ JointSizeAtMost D F I k}

/-- The single least size of output `i` on `D`. -/
noncomputable def singleSize {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) (i : Fin m) : ℕ∞ :=
  jointSize D F {i}

/-- The subfamily `I` saves: its joint least size is below the sum of its single least sizes. -/
def Saves {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) : Prop :=
  jointSize D F I < ∑ i ∈ I, singleSize D F i

/-- The sharing order: the least number of outputs of a saving subfamily, `⊤` if none saves. -/
noncomputable def sharingOrder {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ I : Finset (Fin m), (I.card : ℕ∞) = k ∧ Saves D F I}

/-- The AND of the inputs in `S` (`true` when `S` is empty). -/
def andOf {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i ∈ S, x i = true)

/-- The inputs on `n` bits with at least `a` and at most `b` true bits. -/
def weightBand (n a b : ℕ) : Set (Fin n → Bool) :=
  {x | a ≤ (univ.filter fun i => x i = true).card ∧ (univ.filter fun i => x i = true).card ≤ b}

end PEqualNP.CircuitLowerBounds

end SharingOrder

section LiteralPartition

/-!
# Literal-rectangle partition number of a Boolean function

Let `f` be a Boolean function on `n` inputs. A pair is an input `x` with `f x = true` together
with an input `y` with `f y = false`. A literal rectangle is a set of pairs of the form `A × B`
(with `A` inside the inputs where `f` is true and `B` inside the inputs where `f` is false)
together with a literal: a position `i` and a bit `b` such that every `x` in `A` has `x i = b`
and every `y` in `B` has `y i` different from `b`. The literal-rectangle partition number of
`f` is the least `k` such that the set of all pairs is the disjoint union of `k` literal
rectangles. It sits between the typed rank of `Defs/MetaComplexityTypedRank.lean` and the de
Morgan leaf size of `Defs/DeMorganFormula.lean`.

* `IsLiteralPartition n f k A B pos bit`: the `k` rectangles `A j × B j`, each with the literal
  `(pos j, bit j)`, partition the pairs of `f`.
* `HasLiteralPartition n f k`: the pairs of `f` split into at most `k` literal rectangles.

Caveats a statement must respect.
* "At most `k`": empty rectangles are allowed, so `HasLiteralPartition n f k` is monotone in
  `k`, and the number itself is the least `k` for which it holds.
* The literal of a rectangle constrains only the pairs it contains: the condition is stated
  for each `x` in `A j` and `y` in `B j` together, so a rectangle with `A j` or `B j` empty
  places no condition on its literal. This is the reading of a rectangle as a set of pairs.
* Positions are natural numbers, not elements of `Fin n`, so that a partition into `k > 0`
  (empty) parts exists when `n = 0` (then `f` is constant and there is no pair). A rectangle
  holding a pair has its position below `n`.
* Partition means every pair lies in exactly one rectangle; a cover is not enough.

Nothing here speaks of formulas or ranks; the module imports only Mathlib.
-/

namespace PEqualNP.MetaComplexity

/-- The `k` rectangles `A j × B j` with literals `(pos j, bit j)` form a literal partition of the
pairs of `f`:
* every member of `A j` is an input where `f` is true, every member of `B j` an input where `f`
  is false;
* for `x` in `A j` and `y` in `B j`, the position `pos j` is some `i : Fin n` with
  `x i = bit j` and `y i ≠ bit j`;
* every pair `(x, y)` with `f x = true` and `f y = false` lies in exactly one rectangle. -/
def IsLiteralPartition (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ)
    (A B : Fin k → (Fin n → Bool) → Bool) (pos : Fin k → ℕ) (bit : Fin k → Bool) : Prop :=
  (∀ j : Fin k, ∀ x : Fin n → Bool, A j x = true → f x = true) ∧
  (∀ j : Fin k, ∀ y : Fin n → Bool, B j y = true → f y = false) ∧
  (∀ j : Fin k, ∀ x y : Fin n → Bool, A j x = true → B j y = true →
    ∃ i : Fin n, pos j = (i : ℕ) ∧ x i = bit j ∧ y i ≠ bit j) ∧
  (∀ x y : Fin n → Bool, f x = true → f y = false →
    ∃! j : Fin k, A j x = true ∧ B j y = true)

/-- The pairs of `f` split into at most `k` literal rectangles: the literal-rectangle partition
number of `f` is at most `k`. -/
def HasLiteralPartition (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ (A B : Fin k → (Fin n → Bool) → Bool) (pos : Fin k → ℕ) (bit : Fin k → Bool),
    IsLiteralPartition n f k A B pos bit

end PEqualNP.MetaComplexity

end LiteralPartition

section PairShadow

/-!
# The pair shadow of a gate, and shadow-free AND/OR circuits on a graph

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n`: wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`, and a gate reads the
wires named in its input list (a wire that does not exist yet reads `false`). The inputs are the
vertices of a graph `G` on `Fin n`; the circuit is meant to compute the edge function of `G`
(true exactly when both ends of some edge are true), `graphFun G ∅` of the nested cover module.

The object (a notion of the fleet, founders' point 0i). Let `1_u` be the input true exactly at
`u` and `1_uv` the input true exactly at `u` and `v`. The PAIR SHADOW of gate `j` is the set of
NON-EDGE pairs `{u, v}`, `u ≠ v`, such that gate `j` is true at `1_uv` and false at both `1_u`
and `1_v`. For a monotone gate these are exactly the two-element prime implicants of the gate
that are not edges of `G`. The circuit is SHADOW-FREE when every gate has an empty shadow.

* `unitInput u`: the input `1_u`, true exactly at `u`.
* `InShadow n G C j u v`: the pair `u, v` lies in the pair shadow of gate `j` (wire `n + j`).
* `ShadowFree n G C`: no gate of `C` has a pair in its shadow.
* `shadowGates n G C`: the gate indices, in order, whose shadow is not empty.
* `shadowCount n G C`: the number of those gates.

The pair input `1_uv` is `pairInput u v` and the gate value is `gateVal n C j x`, both of the
edge ownership module (`PEqualNP.Defs.EdgeOwnership`); the graph of a small row is written with
its `edgeGraph`.

Caveats a statement must respect.
* Gate index `j` is wire `n + j`: the number of inputs `n` is an argument and must be the `n`
  of the circuit's input list. Input wires carry no shadow (they are not gates here).
* A wire that does not exist reads `false`, so a gate index at or past `C.gates.length` is false
  at `1_uv` and has an empty shadow; `ShadowFree` quantifies over existing gates only, which is
  the same thing.
* `InShadow` is stated on ORDERED vertices `u, v` but is symmetric in them (a lemma of the
  scratch helper): the shadow of a gate, as a set of unordered pairs, is read off either order.
  It requires `u ≠ v` and `¬ G.Adj u v`.
* The definition reads only the inputs of weight one and two; it does not itself require `C`
  to compute the edge function of `G`, to be monotone, of fan-in two, or to use only AND and
  OR gates: state those as hypotheses (`circuitFun n C = graphFun G ∅`, `AndOrOnly C`, ...).
  For a gate with NOT gates below it the "prime implicant" reading is lost; the 2-slice reading
  stays the definition.
* Counts (`shadowCount`, `invisibleCount`) include gates no output depends on, so "at least `k`
  such gates" can be met by padding a circuit: speak of least circuits, or count only gates an
  output depends on.
-/

namespace PEqualNP.PairShadow

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

/-- The input `1_u` on `Fin n`: true exactly at `u`. -/
def unitInput {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun w => decide (w = u)

/-- The pair `u, v` lies in the PAIR SHADOW of gate `j` of `C` (wire `n + j`) with respect to
`G`: `u ≠ v`, `uv` is not an edge of `G`, the gate is true at `1_uv` and false at `1_u` and at
`1_v`. -/
def InShadow (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
    gateVal n C j (unitInput u) = false ∧ gateVal n C j (unitInput v) = false

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (u v : Fin n) : Decidable (InShadow n G C j u v) := by
  unfold InShadow; infer_instance

/-- `C` is SHADOW-FREE with respect to `G`: no gate of `C` has a pair in its shadow. -/
def ShadowFree (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ u v : Fin n, ¬ InShadow n G C j u v

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Decidable (ShadowFree n G C) := by
  unfold ShadowFree; infer_instance

/-- The indices, in order, of the gates of `C` whose pair shadow is not empty. -/
def shadowGates (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    List ℕ :=
  (List.range C.gates.length).filter fun j => decide (∃ u v : Fin n, InShadow n G C j u v)

/-- The number of gates of `C` whose pair shadow is not empty. -/
def shadowCount (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : ℕ :=
  (shadowGates n G C).length

end PEqualNP.PairShadow

end PairShadow
