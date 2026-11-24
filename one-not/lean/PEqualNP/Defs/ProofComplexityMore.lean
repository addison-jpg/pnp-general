import PEqualNP.Defs.ProofComplexityLin
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Defs
import PEqualNP.Defs.ProofComplexityPC
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs.ProofComplexity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Basic
import Mathlib.Order.SymmDiff

section ProofComplexityBit

/-!
# Definitions of the proof complexity program: the bit pigeonhole principle and linear rank

* `BPHP m l`: the bit (binary) pigeonhole formula with `m` pigeons and `2 ^ l` holes, where
  each pigeon names its hole by `l` bits.
* `linRank C`: the rank, over the field with two elements, of the set of linear forms that
  occur in the linear clause `C`. This is the rank of the linear system that is the negation
  of `C`, the width measure of Res(⊕) used by Efremenko, Garlik and Itsykson (STOC 2024).
-/

namespace PEqualNP.ProofComplexity

/-- The bit pigeonhole formula with `m` pigeons and `2 ^ l` holes. The variable `(i, b)` is
bit `b` of the hole of pigeon `i`, so an assignment sends each pigeon to a hole, a string of
`l` bits. The clauses: for each two different pigeons `i`, `i'` and each hole `α`, the clause
"not both `i` and `i'` go to `α`", that is, some bit of `i` or some bit of `i'` differs from
the matching bit of `α`. It is unsatisfiable exactly when `m > 2 ^ l`. -/
def BPHP (m l : ℕ) : Set (Clause (Fin m × Fin l)) :=
  {C | ∃ (i i' : Fin m) (α : Fin l → Bool), i ≠ i' ∧
    C = Finset.univ.image (fun b : Fin l => ((i, b), !α b)) ∪
        Finset.univ.image (fun b : Fin l => ((i', b), !α b))}

/-- The rank of a linear clause: the dimension, over the field with two elements, of the
span of the linear forms of its equations, each form `f` read as its indicator vector in
`V → ZMod 2`. The right-hand sides of the equations play no role. The empty clause has rank
`0`, and a clause that comes from an ordinary clause has rank equal to its number of
variables. -/
noncomputable def linRank {V : Type} [DecidableEq V] (C : LinClause V) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
    ((fun q : LinEq V => (fun v : V => if v ∈ q.1 then (1 : ZMod 2) else 0)) ''
      (C : Set (LinEq V))))

end PEqualNP.ProofComplexity

end ProofComplexityBit

section ProofComplexityChain

/-!
# Draft definitions for the chain from Res(⊕) to polynomial calculus on bit pigeonhole

Draft, not part of the definitions root. These are the extra notions needed to state the
links of the proof chain of arXiv:2609.23015 (unrefereed) on our own definitions:

* `IsRowLinear m l k f`: the polynomial `f` in the bit variables is row-linear of degree at
  most `k`.
* `bitDecoder m l`: the substitution that reads bit variables as sums of one-hot variables.
* `BlockVar`, `blockProduct`, `blockSystem`: a base system extended by a family of blocks
  with fresh coefficient variables.
-/

namespace PEqualNP.ProofComplexity

open MvPolynomial

/-- `IsRowLinear m l k f`: every monomial of `f` has total degree at most `k` and uses at most
one bit variable of each pigeon `i`, with exponent one (the exponents of the row of `i` sum to
at most one). The zero polynomial and the constants are row-linear for every `k`. This is the
same condition as membership in the helper submodule `Helpers.rowLinear m l k`, whose carrier
is the set of polynomials with support inside the same set of exponent vectors. -/
def IsRowLinear (m l k : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)) : Prop :=
  ∀ u ∈ f.support, (u.sum fun _ e => e) ≤ k ∧ ∀ i : Fin m, ∑ t : Fin l, u (i, t) ≤ 1

/-- The bit decoder. A hole `j : Fin (2 ^ l)` is read as the string of `l` bits of the number
`j`. The decoder is the algebra map that sends the bit variable `(i, t)` to the sum of the
one-hot variables `(i, j)` over the holes `j` whose bit `t` is set. At a one-hot point (pigeon
`i` in exactly one hole) this sum is bit `t` of the hole of pigeon `i`. -/
noncomputable def bitDecoder (m l : ℕ) :
    MvPolynomial (Fin m × Fin l) (ZMod 2) →ₐ[ZMod 2]
      MvPolynomial (Fin m × Fin (2 ^ l)) (ZMod 2) :=
  aeval fun v : Fin m × Fin l =>
    ∑ j : Fin (2 ^ l), if j.val.testBit v.2.val = true then X (v.1, j) else 0

/-- The variables of a base system on `V` extended by `M` blocks of accuracy `h`, each with
`W` inputs: an old variable `Sum.inl v`, or the coefficient variable `Sum.inr (j, u, i)` of
block `j : Fin M`, factor `u : Fin h` and input `i : Fin W`. Different blocks have different
coefficient variables. All blocks have the same number `W` of inputs; a block with fewer
inputs is padded with zero inputs, which changes nothing (see `blockSystem`). -/
abbrev BlockVar (V : Type) (h M W : ℕ) : Type := V ⊕ (Fin M × Fin h × Fin W)

/-- The product of block `j`: over the `h` factors `u`, the product of
`1 + ∑ i, r (j, u, i) * g j i`, where `r` are the coefficient variables of the block and
`g j i` are its inputs, polynomials in the old variables (over `ZMod 2` the sign of the sum
does not matter). With `h = 0`, or with all inputs zero, the product is `1`. -/
noncomputable def blockProduct {V : Type} (h M W : ℕ)
    (g : Fin M → Fin W → MvPolynomial V (ZMod 2)) (j : Fin M) :
    MvPolynomial (BlockVar V h M W) (ZMod 2) :=
  ∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) * rename Sum.inl (g j i))

/-- The base system `F` on the old variables `V` extended by the `M` blocks with inputs `g`
and accuracy `h`. It consists of

* every polynomial of `F`, read in the old variables;
* the Boolean axiom `X r * X r + X r` for every coefficient variable `r`;
* for every block `j` and input `i`, the companion `g j i * blockProduct h M W g j`.

The block product itself is not an axiom. At a Boolean point the companions say: if some
input of block `j` is `1` then the product of block `j` is `0`. A zero input contributes the
zero polynomial as a companion and coefficient variables that occur in no other axiom except
their own Boolean axioms. The inputs are arbitrary polynomials here; statements add the
hypothesis that they are affine (`totalDegree ≤ 1`). -/
def blockSystem {V : Type} (F : Set (MvPolynomial V (ZMod 2))) (h M W : ℕ)
    (g : Fin M → Fin W → MvPolynomial V (ZMod 2)) :
    Set (MvPolynomial (BlockVar V h M W) (ZMod 2)) :=
  {p | (∃ q ∈ F, p = rename Sum.inl q) ∨
    (∃ r : Fin M × Fin h × Fin W, p = X (Sum.inr r) * X (Sum.inr r) + X (Sum.inr r)) ∨
    ∃ (j : Fin M) (i : Fin W), p = rename Sum.inl (g j i) * blockProduct h M W g j}

end PEqualNP.ProofComplexity

end ProofComplexityChain

section ProofComplexityGeneral

/-!
# Definitions of the proof complexity program: a CNF formula as a polynomial system

The standard translation of clauses to polynomials over the two-element field, used to state
the general link between resolution over linear equations and polynomial calculus degree.
The ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

open MvPolynomial

/-- The polynomial of a clause: the product, over its literals, of `1 + X v` for a positive
literal `(v, true)` and of `X v` for a negative literal `(v, false)`. At a point of the cube
it is `1` exactly when the clause is false, so the equation "polynomial = 0" says the clause
holds. The empty clause has polynomial `1`. Its degree is at most the number of literals. -/
noncomputable def clausePoly {V : Type} (C : Clause V) : MvPolynomial V (ZMod 2) :=
  ∏ l ∈ C, (if l.2 = true then 1 + X l.1 else X l.1)

/-- The polynomial system of a set of clauses: the Boolean axiom `X v * X v + X v` for every
variable `v`, and the polynomial of every clause. A point is a common zero exactly when it is
a satisfying assignment. -/
def cnfSystem {V : Type} (F : Set (Clause V)) : Set (MvPolynomial V (ZMod 2)) :=
  {p | (∃ v : V, p = X v * X v + X v) ∨ ∃ C ∈ F, p = clausePoly C}

end PEqualNP.ProofComplexity

end ProofComplexityGeneral

section ProofComplexityLift

/-!
# Definitions of the proof complexity program: lifting by the inner-product gadget

A CNF formula `F` on variables `V` is lifted by replacing each variable by the inner product
`y₀ y₁ + y₂ y₃` (mod 2) of a block of four fresh bits `(v, 0), …, (v, 3)`. The lifted formula is
not fixed here as one clause set: `IsIPLiftOf F G` says only what every encoding of the lift
satisfies, that an assignment falsifying a clause of `G` falsifies, through the gadget, a clause
of `F`. The two measures at the end read a Res(⊕) line as it is written, equation by equation:
the blocks cut by equations that stay inside one block, and the number of (equation, block)
incidences of the equations that touch two or more blocks. The ruling is in
`ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- The gadget: the inner product of two pairs of bits, `y₀ y₁ + y₂ y₃` modulo 2. -/
def ipGadget (y : Fin 4 → Bool) : Bool := xor (y 0 && y 1) (y 2 && y 3)

/-- The assignment of the variables of `F` induced by an assignment of the lifted bits: the
value of `v` is the gadget applied to the block of `v`. -/
def liftAssign {V : Type} (a : V × Fin 4 → Bool) : V → Bool :=
  fun v => ipGadget (fun j => a (v, j))

/-- `G`, a clause set on the lifted bits, is (an encoding of) the lift of `F` by the gadget:
every assignment that falsifies a clause of `G` induces an assignment that falsifies a clause
of `F`. -/
def IsIPLiftOf {V : Type} (F : Set (Clause V)) (G : Set (Clause (V × Fin 4))) : Prop :=
  ∀ D ∈ G, ∃ C ∈ F, ∀ a : V × Fin 4 → Bool, ¬ ClauseSat a D → ¬ ClauseSat (liftAssign a) C

/-- The blocks an equation touches. -/
def eqBlocks {V : Type} [DecidableEq V] (q : LinEq (V × Fin 4)) : Finset V :=
  q.1.image Prod.fst

/-- The blocks cut by the block-local equations of a line: the blocks `v` such that some
equation of the line touches the block `v` and no other block. -/
def lineLocalBlocks {V : Type} [DecidableEq V] (L : LinClause (V × Fin 4)) : Finset V :=
  (L.filter (fun q => (eqBlocks q).card = 1)).biUnion eqBlocks

/-- The cross-block incidence of a line: the sum, over its equations that touch two or more
blocks, of the number of blocks touched. -/
def lineCrossInc {V : Type} [DecidableEq V] (L : LinClause (V × Fin 4)) : ℕ :=
  (L.filter (fun q => 2 ≤ (eqBlocks q).card)).sum (fun q => (eqBlocks q).card)

end PEqualNP.ProofComplexity

end ProofComplexityLift

section ProofComplexityLinK

/-!
# Definitions of the proof complexity program: Res(k, ⊕)

Resolution whose lines are disjunctions of conjunctions of at most `k` linear equations over
the field with two elements: the system that extends Res(⊕) (the case `k = 1`) the way the
`k`-DNF resolution Res(k) of Krajicek (Fund. Math. 170, 2001) extends resolution. Rules: cut on
a term, and-introduction, and weakening.

The weakening relation is a parameter of the derivation predicate, because the choice matters.
With FULL semantic weakening (`LinKSemWeak`) the system is trivial once `k` reaches the clause
width: the line whose terms say "clause `i` is false" is a tautology, and one cut against each
axiom empties it. The system we study uses `IsLinKWeakening`: term by term, a term of the
premise implies one term of the conclusion, or implies the disjunction of the one-equation
terms of the conclusion. At `k = 1` this is exactly the semantic weakening of Res(⊕). The
ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- A term: a finite set of linear equations, read as their conjunction. The empty term is
true. -/
abbrev LinTerm (V : Type) : Type := Finset (LinEq V)

/-- A line of Res(k, ⊕): a finite set of terms, read as their disjunction. The empty line is
false. -/
abbrev LinKLine (V : Type) : Type := Finset (LinTerm V)

/-- The assignment `a` satisfies the term `T`: it satisfies every equation of `T`. -/
def LinTermSat {V : Type} (a : V → Bool) (T : LinTerm V) : Prop :=
  ∀ q ∈ T, LinEqSat a q

/-- The assignment `a` satisfies the line `L`: it satisfies some term of `L`. -/
def LinKLineSat {V : Type} (a : V → Bool) (L : LinKLine V) : Prop :=
  ∃ T ∈ L, LinTermSat a T

/-- The complementary equation: `f = b` becomes `f = b + 1`. -/
def negLinEq {V : Type} (q : LinEq V) : LinEq V := (q.1, !q.2)

/-- A clause as a line: one one-equation term `{v = s}` for each literal `(v, s)`. -/
def linKOfClause {V : Type} [DecidableEq V] (C : Clause V) : LinKLine V :=
  (linOfClause C).image (fun q => ({q} : LinTerm V))

/-- The cut rule: `C` holds the term `T`, `D` holds the one-equation term of the complement of
every equation of `T`, and `R` is the rest of `C` together with the rest of `D`. -/
def IsLinKCut {V : Type} [DecidableEq V] (C D R : LinKLine V) : Prop :=
  ∃ T : LinTerm V, T ∈ C ∧ (∀ e ∈ T, ({negLinEq e} : LinTerm V) ∈ D) ∧
    R = C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))

/-- And-introduction: from `C` holding `T₁` and `D` holding `T₂`, the rest of both together
with the term `T₁ ∪ T₂`. -/
def IsLinKAndIntro {V : Type} [DecidableEq V] (C D R : LinKLine V) : Prop :=
  ∃ T₁ T₂ : LinTerm V, T₁ ∈ C ∧ T₂ ∈ D ∧ R = (C.erase T₁ ∪ D.erase T₂) ∪ {T₁ ∪ T₂}

/-- Termwise weakening: every term of `L` implies a single term of `M`, or implies the
disjunction of the one-equation terms of `M`. -/
def IsLinKWeakening {V : Type} (L M : LinKLine V) : Prop :=
  ∀ T ∈ L, (∃ S ∈ M, ∀ a : V → Bool, LinTermSat a T → LinTermSat a S) ∨
    (∀ a : V → Bool, LinTermSat a T → ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)

/-- Full semantic weakening: every assignment satisfying `L` satisfies `M`. Named only to
state that it makes the system trivial. -/
def LinKSemWeak {V : Type} (L M : LinKLine V) : Prop :=
  ∀ a : V → Bool, LinKLineSat a L → LinKLineSat a M

/-- `IsLinKDerivation k W F π`: the list `π`, NEWEST LINE FIRST, is a derivation from the lines
`F` in which every term of every line has at most `k` equations. Each line is a line of `F`,
or follows from two lines after it in the list by cut or by and-introduction, or from one line
after it by the weakening relation `W`. The number of lines is `π.length`. -/
inductive IsLinKDerivation {V : Type} [DecidableEq V] (k : ℕ)
    (W : LinKLine V → LinKLine V → Prop) (F : Set (LinKLine V)) : List (LinKLine V) → Prop
  | nil : IsLinKDerivation k W F []
  | ax {π : List (LinKLine V)} {C : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ F → (∀ T ∈ C, T.card ≤ k) →
      IsLinKDerivation k W F (C :: π)
  | cut {π : List (LinKLine V)} {C D R : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → D ∈ π → IsLinKCut C D R → (∀ T ∈ R, T.card ≤ k) →
      IsLinKDerivation k W F (R :: π)
  | andIntro {π : List (LinKLine V)} {C D R : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → D ∈ π → IsLinKAndIntro C D R →
      (∀ T ∈ R, T.card ≤ k) → IsLinKDerivation k W F (R :: π)
  | weak {π : List (LinKLine V)} {C D : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → W C D → (∀ T ∈ D, T.card ≤ k) →
      IsLinKDerivation k W F (D :: π)

/-- A Res(k, ⊕) refutation of the CNF formula `F`, with termwise weakening: a derivation from
the clauses of `F`, read as lines, that contains the empty line. -/
def IsLinKRefutation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (Clause V))
    (π : List (LinKLine V)) : Prop :=
  IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) π ∧ (∅ : LinKLine V) ∈ π

end PEqualNP.ProofComplexity

end ProofComplexityLinK

section ProofComplexityMoment

/-!
# Definitions of the proof complexity program: matching moments

Families of values in the two-element field on partial matchings of pigeons to holes. They
are the dual objects of degree-bounded polynomial calculus on the functional pigeonhole
system: a consistent family is a linear functional that kills every static consequence.
The ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- A partial matching of `m` pigeons to `N` holes: a finite set of pairs in which two
different pairs share neither their pigeon nor their hole. -/
def IsPartialMatching {m N : ℕ} (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

/-- The family `z` is consistent up to size `k`: for every partial matching `T` with fewer
than `k` pairs and every pigeon `i` not in `T`, the value at `T` is the sum, over the holes
`j` not used by `T`, of the values at `T` with the pair `(i, j)` added. Only the values of `z`
on partial matchings of at most `k` pairs matter. -/
def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

/-- The extension property at level `k`: every family consistent up to size `k` agrees, on
partial matchings of at most `k` pairs, with a family consistent up to size `k + 1`. -/
def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

end PEqualNP.ProofComplexity

end ProofComplexityMoment

section ProofComplexityResK

/-!
# Definitions of the proof complexity program: k-DNF resolution Res(k)

The system Res(k) of Krajicek (Fund. Math. 170, 2001), in the form of Segerlind, Buss and
Impagliazzo (SIAM J. Comput. 33, 2004): lines are k-DNFs, that is, disjunctions of conjunctions
of at most `k` literals. Rules: weakening (add terms), and-introduction, and-elimination, and
cut of a conjunction against the negations of its literals. All rules are syntactic. It is here
as a yardstick: Res(k, ⊕) of `Defs/ProofComplexityLinK.lean` is meant to contain it.
-/

namespace PEqualNP.ProofComplexity

/-- A term of a k-DNF: a finite set of literals, read as their conjunction. -/
abbrev KTerm (V : Type) : Type := Finset (Literal V)

/-- A line of Res(k): a finite set of terms, read as their disjunction. -/
abbrev KLine (V : Type) : Type := Finset (KTerm V)

/-- The assignment `a` satisfies the line `L`: it makes every literal of some term true. -/
def KLineSat {V : Type} (a : V → Bool) (L : KLine V) : Prop :=
  ∃ T ∈ L, ∀ l ∈ T, a l.1 = l.2

/-- A clause as a line: one one-literal term for each literal. -/
def kLineOfClause {V : Type} [DecidableEq V] (C : Clause V) : KLine V :=
  C.image (fun l => ({l} : KTerm V))

/-- Weakening: `M` holds every term of `L`. -/
def IsResKWeakening {V : Type} (L M : KLine V) : Prop := L ⊆ M

/-- And-introduction: from `C` holding `T₁` and `D` holding `T₂`, the rest of both together
with the term `T₁ ∪ T₂`. -/
def IsResKAndIntro {V : Type} [DecidableEq V] (C D R : KLine V) : Prop :=
  ∃ T₁ T₂ : KTerm V, T₁ ∈ C ∧ T₂ ∈ D ∧ R = (C.erase T₁ ∪ D.erase T₂) ∪ {T₁ ∪ T₂}

/-- And-elimination: a term `T` of `C` is replaced by a nonempty part `T'` of it. -/
def IsResKAndElim {V : Type} [DecidableEq V] (C R : KLine V) : Prop :=
  ∃ T T' : KTerm V, T ∈ C ∧ T' ⊆ T ∧ T'.Nonempty ∧ R = C.erase T ∪ {T'}

/-- Cut: `C` holds the term `T`, `D` holds the one-literal term of the negation of every
literal of `T`, and `R` is the rest of `C` together with the rest of `D`. -/
def IsResKCut {V : Type} [DecidableEq V] (C D R : KLine V) : Prop :=
  ∃ T : KTerm V, T ∈ C ∧ T.Nonempty ∧ (∀ l ∈ T, ({(l.1, !l.2)} : KTerm V) ∈ D) ∧
    R = C.erase T ∪ (D \ T.image (fun l => ({(l.1, !l.2)} : KTerm V)))

/-- `IsResKDerivation k F π`: the list `π`, NEWEST LINE FIRST, is a Res(k) derivation from the
lines `F`; every term of every line has at most `k` literals. The number of lines is
`π.length`. -/
inductive IsResKDerivation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (KLine V)) :
    List (KLine V) → Prop
  | nil : IsResKDerivation k F []
  | ax {π : List (KLine V)} {C : KLine V} :
      IsResKDerivation k F π → C ∈ F → (∀ T ∈ C, T.card ≤ k) → IsResKDerivation k F (C :: π)
  | weak {π : List (KLine V)} {C D : KLine V} :
      IsResKDerivation k F π → C ∈ π → IsResKWeakening C D → (∀ T ∈ D, T.card ≤ k) →
      IsResKDerivation k F (D :: π)
  | andIntro {π : List (KLine V)} {C D R : KLine V} :
      IsResKDerivation k F π → C ∈ π → D ∈ π → IsResKAndIntro C D R → (∀ T ∈ R, T.card ≤ k) →
      IsResKDerivation k F (R :: π)
  | andElim {π : List (KLine V)} {C R : KLine V} :
      IsResKDerivation k F π → C ∈ π → IsResKAndElim C R → IsResKDerivation k F (R :: π)
  | cut {π : List (KLine V)} {C D R : KLine V} :
      IsResKDerivation k F π → C ∈ π → D ∈ π → IsResKCut C D R → IsResKDerivation k F (R :: π)

/-- A Res(k) refutation of the CNF formula `F`: a derivation from the clauses of `F`, read as
lines, that contains the empty line. -/
def IsResKRefutation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (Clause V))
    (π : List (KLine V)) : Prop :=
  IsResKDerivation k ((fun C => kLineOfClause C) '' F) π ∧ (∅ : KLine V) ∈ π

end PEqualNP.ProofComplexity

end ProofComplexityResK

section ProofComplexityRestrict

/-!
# Definitions of the proof complexity program: restriction of a CNF by a partial assignment

A partial assignment `ρ : V → Option Bool` sets the variables `v` with `ρ v = some b` and
leaves the variables with `ρ v = none` free. Restricting a clause by `ρ`: if `ρ` makes some
literal of the clause true, the clause is satisfied and disappears; otherwise the literals on
set variables (all false under `ρ`) are removed and the literals on free variables remain.
Variable names do not change: the restricted formula is a set of clauses on the same type `V`
in which set variables no longer occur.

Instance in use: setting every pigeonhole variable outside the edges of a bipartite graph to
false turns the pigeonhole formula into the graph pigeonhole formula of that graph.
-/

namespace PEqualNP.ProofComplexity

/-- The restriction of the clause `C` by the partial assignment `ρ`: `none` when `ρ` makes some
literal of `C` true, otherwise the literals of `C` on the variables `ρ` leaves free. -/
def restrictClause {V : Type} [DecidableEq V] (ρ : V → Option Bool) (C : Clause V) :
    Option (Clause V) :=
  if ∃ l ∈ C, ρ l.1 = some l.2 then none else some (C.filter fun l => ρ l.1 = none)

/-- The restriction of the CNF formula `F` by `ρ`: the restrictions of its clauses that `ρ`
does not satisfy. -/
def restrictCNF {V : Type} [DecidableEq V] (F : Set (Clause V)) (ρ : V → Option Bool) :
    Set (Clause V) :=
  {C' | ∃ C ∈ F, restrictClause ρ C = some C'}

end PEqualNP.ProofComplexity

end ProofComplexityRestrict

section Expanders

/-!
# Bipartite graphs, boundary expansion, and pigeonhole formulas on a graph

Needed by the proof complexity chain to L-pcx-017 (Res(+) lower bounds for the pigeonhole
formula through polynomial calculus degree on an expander). The pinned Mathlib has no
bipartite expanders.

* A bipartite graph with left vertices `Fin m` (pigeons) and right vertices `Fin N` (holes) is
  the neighbourhood of each left vertex, `BipGraph m N := Fin m → Finset (Fin N)`.
* The unique neighbours of a left set `T`: the right vertices with exactly one neighbour in `T`.
  `G` is an `(s, δ)` boundary expander when every left set of at most `s` vertices has at least
  `δ` times as many unique neighbours as it has vertices.
* The variables of a pigeonhole formula on `G` are its edges, `GEdge G`, so that the number of
  variables is the number of edges (on the complete graph it would be quadratic).
* `graphPHP G`: for each pigeon, "it sits in some neighbouring hole"; for each hole and two
  different neighbouring pigeons, "not both". This is exactly what restricting `PHP` to the
  edges of `G` gives. `funGraphPHP G` adds, for each pigeon and two different neighbouring
  holes, "not both" (the functional version).
-/

namespace PEqualNP.Expanders

open PEqualNP.ProofComplexity

/-- A bipartite graph with left vertices `Fin m` and right vertices `Fin N`, given by the
neighbourhood of each left vertex. -/
abbrev BipGraph (m N : ℕ) : Type := Fin m → Finset (Fin N)

/-- The left neighbours of the right vertex `j`. -/
def rightNbrs {m N : ℕ} (G : BipGraph m N) (j : Fin N) : Finset (Fin m) :=
  Finset.univ.filter (fun i => j ∈ G i)

/-- Every left vertex has at most `b` neighbours. -/
def LeftDegLe {m N : ℕ} (G : BipGraph m N) (b : ℕ) : Prop :=
  ∀ i, (G i).card ≤ b

/-- Every right vertex has at most `b` neighbours. -/
def RightDegLe {m N : ℕ} (G : BipGraph m N) (b : ℕ) : Prop :=
  ∀ j, (rightNbrs G j).card ≤ b

/-- The unique neighbours of the left set `T`: right vertices with exactly one neighbour in `T`. -/
def uniqueNbrs {m N : ℕ} (G : BipGraph m N) (T : Finset (Fin m)) : Finset (Fin N) :=
  Finset.univ.filter (fun j => (T.filter (fun i => j ∈ G i)).card = 1)

/-- `G` is an `(s, δ)` boundary expander: every left set of at most `s` vertices has at least
`δ` times its size in unique neighbours. -/
def IsBdryExpander {m N : ℕ} (G : BipGraph m N) (s δ : ℕ) : Prop :=
  ∀ T : Finset (Fin m), T.card ≤ s → δ * T.card ≤ (uniqueNbrs G T).card

/-- The edges of `G`: pairs (pigeon, hole) with the hole a neighbour of the pigeon. -/
abbrev GEdge {m N : ℕ} (G : BipGraph m N) : Type := {e : Fin m × Fin N // e.2 ∈ G e.1}

/-- The pigeonhole formula on `G`, variables the edges: each pigeon sits in a neighbouring hole,
and no hole holds two different pigeons. -/
def graphPHP {m N : ℕ} (G : BipGraph m N) : Set (Clause (GEdge G)) :=
  {C | ∃ i : Fin m, C = Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)} ∪
  {C | ∃ (e e' : GEdge G), e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ C = {(e, false), (e', false)}}

/-- The functional pigeonhole formula on `G`: `graphPHP G` and, for each pigeon, not two
different holes. -/
def funGraphPHP {m N : ℕ} (G : BipGraph m N) : Set (Clause (GEdge G)) :=
  graphPHP G ∪
  {C | ∃ (e e' : GEdge G), e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ C = {(e, false), (e', false)}}

end PEqualNP.Expanders

end Expanders

section SearchRUP

/-!
# Definitions of the P = NP algorithm search: clause learning by unit propagation

A model of the unsatisfiable runs of CDCL solvers that is independent of decisions, restarts
and deletion: the solver learns a sequence of clauses, each of which is RUP (reverse unit
propagation) with respect to the input and the clauses learned before it: assuming every
literal of the clause false, unit propagation falsifies some known clause. Every learning
scheme in use (any cut of the implication graph, first UIP, decision learning, clause
minimization) learns RUP clauses (Beame, Kautz and Sabharwal 2004). A run ends in an
unsatisfiability proof when it learns the empty clause.
-/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- The complementary literal. -/
def negLit {V : Type} (l : Literal V) : Literal V := (l.1, !l.2)

/-- `UPForces Γ A l`: unit propagation over the clauses `Γ`, from the literals `A` assumed
true, makes `l` true: `l` is assumed, or some clause of `Γ` contains `l` and every other
literal of it is already made false. -/
inductive UPForces {V : Type} (Γ : Set (Clause V)) (A : Set (Literal V)) : Literal V → Prop
  | hyp {l : Literal V} : l ∈ A → UPForces Γ A l
  | unit {D : Clause V} {l : Literal V} : D ∈ Γ → l ∈ D →
      (∀ l' ∈ D, l' ≠ l → UPForces Γ A (negLit l')) → UPForces Γ A l

/-- `C` is RUP over `Γ`: assuming every literal of `C` false, unit propagation over `Γ` makes
every literal of some clause of `Γ` false. -/
def IsRUP {V : Type} (Γ : Set (Clause V)) (C : Clause V) : Prop :=
  ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ (negLit '' (↑C : Set (Literal V))) (negLit l)

/-- `IsRUPRun F ρ`: the clauses `ρ`, NEWEST FIRST, are learned in turn, each RUP over `F`
and the clauses learned before it. Its length is the number of learned clauses. -/
inductive IsRUPRun {V : Type} (F : Set (Clause V)) : List (Clause V) → Prop
  | nil : IsRUPRun F []
  | learn {ρ : List (Clause V)} {C : Clause V} :
      IsRUPRun F ρ → IsRUP (F ∪ {D | D ∈ ρ}) C → IsRUPRun F (C :: ρ)

end PEqualNP.Search

end SearchRUP

section SearchSoS

/-!
# Definitions of the P = NP algorithm search: sum of squares on parity systems

A parity system is a set of equations `(S, b)`: the sum of the variables of `S` is `b` modulo
two. Two ways to refute one:

* by adding equations, every line on at most `d` variables (`XorRefutable`);
* by a sum-of-squares refutation of its polynomial system in sign variables over the reals
  (`SoSRefutable`), where `true` is the sign `-1` and each variable satisfies `x * x = 1`.

In `SoSRefutable P D` the number `D` is HALF the degree of the refutation.
-/

namespace PEqualNP.Search

open MvPolynomial

variable {V : Type}

/-- `XorDerivable F d e`: the equation `e` is obtained from the parity system `F` by adding
equations, every line having at most `d` variables. `ax`: an equation of `F` on at most `d`
variables; `zero`: the trivial equation `0 = 0`; `add`: the sum of two derived lines (symmetric
difference of the variable sets, exclusive or of the right-hand sides), when the sum has at
most `d` variables. -/
inductive XorDerivable [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) :
    PEqualNP.ProofComplexity.LinEq V → Prop
  | ax {e : PEqualNP.ProofComplexity.LinEq V} (he : e ∈ F) (hw : e.1.card ≤ d) :
      XorDerivable F d e
  | zero : XorDerivable F d (∅, false)
  | add {e e' : PEqualNP.ProofComplexity.LinEq V} (h : XorDerivable F d e)
      (h' : XorDerivable F d e')
      (hw : (symmDiff e.1 e'.1).card ≤ d) :
      XorDerivable F d (symmDiff e.1 e'.1, xor e.2 e'.2)

/-- A refutation of width `d` by adding equations: a derivation of `0 = 1` with every line on
at most `d` variables. -/
def XorRefutable [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) : Prop :=
  XorDerivable F d (∅, true)

/-- The parity equation `(S, b)` as a real polynomial in sign variables: the product of the
variables of `S`, minus `-1` when `b = true` and minus `1` when `b = false`. It stands for the
equation "this polynomial is zero". -/
noncomputable def xorPoly (e : PEqualNP.ProofComplexity.LinEq V) : MvPolynomial V ℝ :=
  (∏ v ∈ e.1, X v) - C (if e.2 = true then -1 else 1)

/-- The polynomial system of a parity system: `X v * X v - 1` for every variable (each variable
is a sign), and the polynomial of every equation. -/
noncomputable def xorSystem (F : Set (PEqualNP.ProofComplexity.LinEq V)) :
    Set (MvPolynomial V ℝ) :=
  {p | ∃ v : V, p = X v * X v - 1} ∪ xorPoly '' F

/-- A sum-of-squares refutation of degree `2 * D` (so `D` is half the degree) of the equations
`p = 0`, `p ∈ P`: polynomials `q_i`, members `p_i` of `P` and polynomials `r_j` with
`∑ q_i * p_i + ∑ r_j * r_j = -1`, every `q_i * p_i` of total degree at most `2 * D` and every
`r_j` of total degree at most `D`. The first sum is a member of the real span of the allowed
products; the second sum is a member of the additive closure of the allowed squares. -/
def SoSRefutable (P : Set (MvPolynomial V ℝ)) (D : ℕ) : Prop :=
  ∃ g ∈ Submodule.span ℝ
      {t : MvPolynomial V ℝ | ∃ p ∈ P, ∃ q : MvPolynomial V ℝ, t = q * p ∧ t.totalDegree ≤ 2 * D},
    ∃ s ∈ AddSubmonoid.closure
      {t : MvPolynomial V ℝ | ∃ r : MvPolynomial V ℝ, r.totalDegree ≤ D ∧ t = r * r},
    g + s = -1

end PEqualNP.Search

end SearchSoS
