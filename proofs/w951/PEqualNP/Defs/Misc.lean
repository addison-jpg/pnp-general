import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import PEqualNP.Defs.Oracle
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import PEqualNP.Defs.Base
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Basic

section AffinePlane

/-!
# The affine plane over a finite field, as a set system

For a finite field `F` with `q = Fintype.card F` elements, the affine plane `F × F` has
`q ^ 2` points and `q ^ 2 + q` lines:

* the non-vertical line of slope `a` and intercept `b`, the points `(x, a * x + b)`
  (`q ^ 2` lines, one per pair `(a, b)`);
* the vertical line at `c`, the points `(c, y)` (`q` lines, one per `c`).

The points at infinity (the projective completion) are left out. Each line has `q` points and
two distinct lines share at most one point.

This module encodes the lines as a family `Fin (q ^ 2 + q) → Finset (Fin (q ^ 2))`, the shape of
the set systems in the rows on Boolean sums (`S : Fin m → Finset (Fin n)`), so a statement on
such a family applies to the plane with no conversion.

Names:
* `AffinePlane.Line F`: the type `(F × F) ⊕ F` of lines; `Sum.inl (a, b)` is the line
  `y = a * x + b`, `Sum.inr c` is the line `x = c`.
* `AffinePlane.lineSet F l`: the points of the line `l`, a `Finset (F × F)`.
* `AffinePlane.pointEquiv F : F × F ≃ Fin (Fintype.card F ^ 2)`: the fixed point encoding.
* `AffinePlane.lineEquiv F : Line F ≃ Fin (Fintype.card F ^ 2 + Fintype.card F)`: the fixed
  line encoding.
* `AffinePlane.affineLines F : Fin (Fintype.card F ^ 2 + Fintype.card F) →
  Finset (Fin (Fintype.card F ^ 2))`: the family of lines, through the two encodings.

Conventions of the encodings (noncomputable):
* `e = Fintype.equivFin F : F ≃ Fin q`, a fixed but unspecified enumeration of `F`.
* The point `(x, y)` is the index `e y + q * e x` (Mathlib's `finProdFinEquiv` on `(e x, e y)`,
  then the cast `q * q = q ^ 2`).
* The non-vertical line `(a, b)` has index `pointEquiv F (a, b)`, below `q ^ 2`; the vertical
  line `c` has index `q ^ 2 + e c` (Mathlib's `finSumFinEquiv`).

Caveats a statement must respect:
* The enumeration `e` is not computable, so `decide` does not see through `affineLines`, even
  for `ZMod 2`; concrete facts come from the general theorems.
* A statement should only use properties that do not depend on the choice of `e` (sizes,
  intersections, incidences), since `e` is fixed but unspecified.
* The number of points is written `Fintype.card F ^ 2`, the number of lines
  `Fintype.card F ^ 2 + Fintype.card F`; the field is a parameter, `q` is never a free number.
* No points at infinity: the projective plane of order `q` has `q ^ 2 + q + 1` points and
  lines, this family has `q ^ 2` points and `q ^ 2 + q` lines.
-/

namespace PEqualNP.AffinePlane

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The lines of the affine plane over `F`: `Sum.inl (a, b)` is the line `y = a * x + b`,
`Sum.inr c` is the vertical line `x = c`. -/
abbrev Line : Type _ := (F × F) ⊕ F

/-- The points of a non-vertical line `y = a * x + b`. -/
def slopeLine (ab : F × F) : Finset (F × F) :=
  Finset.univ.filter (fun p => p.2 = ab.1 * p.1 + ab.2)

/-- The points of a vertical line `x = c`. -/
def verticalLine (c : F) : Finset (F × F) :=
  Finset.univ.filter (fun p => p.1 = c)

/-- The points of the line `l`. -/
def lineSet (l : Line F) : Finset (F × F) :=
  Sum.elim (slopeLine F) (verticalLine F) l

/-- The fixed encoding of the points: `(x, y)` goes to `e y + q * e x` with
`e = Fintype.equivFin F` and `q = Fintype.card F`. -/
noncomputable def pointEquiv : F × F ≃ Fin (Fintype.card F ^ 2) :=
  ((Equiv.prodCongr (Fintype.equivFin F) (Fintype.equivFin F)).trans finProdFinEquiv).trans
    (finCongr (sq (Fintype.card F)).symm)

/-- The fixed encoding of the lines: the line `(a, b)` goes to `pointEquiv F (a, b)`, the
vertical line `c` goes to `q ^ 2 + e c`. -/
noncomputable def lineEquiv : Line F ≃ Fin (Fintype.card F ^ 2 + Fintype.card F) :=
  (Equiv.sumCongr (pointEquiv F) (Fintype.equivFin F)).trans finSumFinEquiv

/-- The affine lines of `F × F` as a set system on `Fintype.card F ^ 2` points:
line number `i` is the set of the codes of its points. -/
noncomputable def affineLines :
    Fin (Fintype.card F ^ 2 + Fintype.card F) → Finset (Fin (Fintype.card F ^ 2)) :=
  fun i => (lineSet F ((lineEquiv F).symm i)).map (pointEquiv F).toEmbedding

end PEqualNP.AffinePlane

end AffinePlane

section Algebraic

/-!
# Extension oracles, for the algebrization barrier

Needed to state the algebrization barrier (Aaronson and Wigderson, ACM Trans. Comput. Theory
1(1), 2009) on this project's oracle machines (`Defs/Oracle.lean`).

* Every finite field is isomorphic to `GaloisField p k` for a prime `p`, so an extension of an
  oracle is given over these fields: `AlgExtension` assigns a polynomial in `m` variables over
  `GaloisField p k` to every prime `p`, every `k` and every arity `m`.
* `IsMultiquadraticExtension A E`: every polynomial of `E` has degree at most 2 in each
  variable, and on the Boolean cube it equals the oracle `A` (a point `x` of `{0,1}^m` is the
  string `List.ofFn x`). Aaronson and Wigderson allow any constant bound on the degree in each
  variable; their separations use 2, and a separation stated with an existential extension of
  degree 2 is one of theirs.
* A machine names a field element by a natural number. `FieldCodes` is a choice of such names,
  one injective map per field. The theorem is stated for EVERY injective choice, so it covers
  any representation in which a machine can compute field operations itself.
* `extOracle codes E` is a language: a query names `p`, `k`, `m`, a point `y` of
  `GaloisField p k ^ m` and a bit position `j`; the answer is bit `j` of the name of the value
  of `E p k m` at `y`. One query reveals one bit of one value; a machine reads a whole value
  with polynomially many queries. Every number is written self-delimiting, so a query string
  names at most one tuple.
-/

namespace PEqualNP.Library

/-- A natural number in binary, self-delimiting: each bit is preceded by `true`, and `false`
ends the number. -/
def algEncodeNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- A family of polynomials: for every prime `p`, every `k` and every arity `m`, a polynomial
in `m` variables over `GaloisField p k`. -/
def AlgExtension : Type :=
  ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ), MvPolynomial (Fin m) (GaloisField p k)

open Classical in
/-- `E` extends the oracle `A` with degree at most 2 in each variable, over every finite
field. Membership in `A` is decided classically. -/
def IsMultiquadraticExtension (A : Language Bool) (E : AlgExtension) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ),
    (∀ i : Fin m, MvPolynomial.degreeOf i (E p k m) ≤ 2) ∧
    ∀ x : Fin m → Bool,
      MvPolynomial.eval (fun i => if x i then (1 : GaloisField p k) else 0) (E p k m) =
        if List.ofFn x ∈ A then 1 else 0

/-- Names of field elements: one map to the naturals for every field `GaloisField p k`. -/
def FieldCodes : Type :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), GaloisField p k → ℕ

/-- Every field's naming map is injective. -/
def FieldCodes.Injective (codes : FieldCodes) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Function.Injective (codes p k)

/-- The oracle that answers bit `j` of the name of `E p k m` at the point `y`. -/
def extOracle (codes : FieldCodes) (E : AlgExtension) : Language Bool :=
  {s | ∃ (p : ℕ) (_ : Fact p.Prime) (k m : ℕ) (y : Fin m → GaloisField p k) (j : ℕ),
      s = algEncodeNat p ++ algEncodeNat k ++ algEncodeNat m ++
          (List.ofFn fun i => algEncodeNat (codes p k (y i))).flatten ++ algEncodeNat j ∧
      (codes p k (MvPolynomial.eval y (E p k m))).testBit j = true}

end PEqualNP.Library

end Algebraic

section BicliqueBlockCost

/-!
# Biclique-block cost of a graph

A BLOCK of a simple graph `G` on `Fin n` is a pair `(A, B)` of disjoint nonempty vertex sets with
every vertex of `A` adjacent to every vertex of `B`. As a circuit it is
`(OR of the inputs of A) AND (OR of the inputs of B)`, with `|A| + |B| - 1` gates, and it is true
exactly on the inputs that switch on some `a ∈ A` and some `b ∈ B`. The BICLIQUE-BLOCK COST
`bc G` is the least value, over finite families of blocks whose pairs together cover every edge
of `G`, of the sum of the block costs plus the number of blocks minus one (the OR gates that join
the blocks). It is the size of one AND/OR circuit for the edge function of `G`.

* `Block n`: a pair of vertex sets `(A, B)`, the candidate blocks.
* `IsBlock G p`: `p.1` and `p.2` are disjoint and nonempty, and `G.Adj a b` for all
  `a ∈ p.1`, `b ∈ p.2`.
* `blockCost p`: `p.1.card + p.2.card - 1`.
* `BlockCovers p u v`: the pair `{u, v}` is split by `p`, one end in `p.1` and the other in `p.2`
  (either way round).
* `IsBlockCover G F`: every member of the finite family `F` is a block of `G`, and every edge of
  `G` is covered by some member of `F`.
* `familyCost F`: the sum of `blockCost` over `F`, plus `F.card - 1`.
* `HasBlockCost G c`: some block cover of `G` has `familyCost` at most `c`. This is the form to
  state rows in; it is decidable when `G.Adj` is.
* `bc G`: the least `c` with `HasBlockCost G c` (an `sInf`, for statements only).

Caveats a statement must respect.

* A family is a `Finset` of blocks, not a list: a repeated block only adds cost, so the least
  value is the same as over lists.
* The pair is ordered: `(A, B)` and `(B, A)` are two blocks with the same cost and the same
  covered edges.
* Subtraction is on `ℕ`. A block has `|A|, |B| ≥ 1`, so `blockCost` is never truncated. The
  family term `F.card - 1` is truncated only for the empty family, which covers only the graph
  with no edge: there `bc = 0`, not `-1`, so the formula `|E| + τ - 1` reads `0` at the empty
  graph as well.
* The decidability instance enumerates all families of pairs of vertex sets, so `decide` is only
  usable to CHECK a given cover (an upper bound); lower bounds need an argument.
* The block cost is an upper bound on the least circuit size only (a cover gives a circuit). It
  is NOT the least size where the graph has a 4-cycle: on small graphs with a 4-cycle a circuit
  below it often exists (computed by script, not checked). Do not read it as a predicted size.
-/

namespace PEqualNP.BicliqueBlockCost

/-- A candidate block on `Fin n`: a pair of vertex sets `(A, B)`. -/
abbrev Block (n : ℕ) : Type := Finset (Fin n) × Finset (Fin n)

/-- `p = (A, B)` is a block of `G`: `A`, `B` disjoint, nonempty, and completely joined. -/
def IsBlock {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) : Prop :=
  Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, G.Adj a b

/-- The gate count of a block: `|A| - 1` ORs, `|B| - 1` ORs and one AND. -/
def blockCost {n : ℕ} (p : Block n) : ℕ :=
  p.1.card + p.2.card - 1

/-- The block `p` covers the pair `{u, v}`: one end in `p.1`, the other in `p.2`. -/
def BlockCovers {n : ℕ} (p : Block n) (u v : Fin n) : Prop :=
  (u ∈ p.1 ∧ v ∈ p.2) ∨ (v ∈ p.1 ∧ u ∈ p.2)

/-- `F` is a family of blocks of `G` covering every edge of `G`. -/
def IsBlockCover {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) : Prop :=
  (∀ p ∈ F, IsBlock G p) ∧ ∀ u v : Fin n, G.Adj u v → ∃ p ∈ F, BlockCovers p u v

/-- The gate count of the OR of the blocks of `F`: the block costs plus `|F| - 1` ORs. -/
def familyCost {n : ℕ} (F : Finset (Block n)) : ℕ :=
  (∑ p ∈ F, blockCost p) + (F.card - 1)

/-- Some block cover of `G` costs at most `c`. -/
def HasBlockCost {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∃ F : Finset (Block n), IsBlockCover G F ∧ familyCost F ≤ c

/-- The biclique-block cost: the least `c` with `HasBlockCost G c`. -/
noncomputable def bc {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | HasBlockCost G c}

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Block n) :
    Decidable (IsBlock G p) := by
  unfold IsBlock; infer_instance

instance {n : ℕ} (p : Block n) (u v : Fin n) : Decidable (BlockCovers p u v) := by
  unfold BlockCovers; infer_instance

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : Finset (Block n)) :
    Decidable (IsBlockCover G F) := by
  unfold IsBlockCover; infer_instance

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : ℕ) :
    Decidable (HasBlockCost G c) := by
  unfold HasBlockCost; infer_instance

end PEqualNP.BicliqueBlockCost

end BicliqueBlockCost

section Classes

/-!
# Further uniform classes: coNP, EXP, NEXP

On top of `Defs/Base.lean` (machines, time bounds, `DTIME`, `P`, `NP`), in the same namespace.
Nothing here is in the pinned Mathlib.

* `coNP`: the complements of the NP languages.
* `EXP`: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`.
* `NEXP`, by verifiers, as `NP` is: a polynomial-time decidable relation with witnesses of
  length at most `2 ^ (n ^ k) + k` for some `k`. The verifier is polynomial in the length of
  the pair, so exponential in the length of the input.

Every bound `2 ^ p(n)` with `p` a polynomial is below `2 ^ (n ^ k) + k` for some `k`, so the
single family of bounds loses nothing.
-/

namespace PEqualNP.Library

/-- coNP: the languages whose complement is in NP. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- EXP: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`. -/
def EXP : Set (Language Bool) :=
  {L | ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)}

/-- NEXP, by verifiers: `L` is in NEXP when there are a polynomial-time decidable set `R` of
pairs (input, witness) and a `k` such that `x` is in `L` exactly when some witness `w` of length
at most `2 ^ (length of x ^ k) + k` has `(x, w)` in `R`. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (k : ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ (x, w) ∈ R}

end PEqualNP.Library

end Classes

section Gct

/-!
# Definitions for geometric complexity theory

The ruling behind this file is `Gct/README.md`. GCT studies the permanent versus the
determinant as polynomials. Mathlib has the determinant and the permanent of a matrix
(`Matrix.det`, `Matrix.permanent`) and the matrix of variables (`Matrix.mvPolynomialX`), and
nothing about determinantal expressions or orbit closures. This file adds the thin layer:

* `detPoly R n`, `permPoly R n`: the determinant and permanent of the `n × n` matrix of
  variables, polynomials in `n²` variables.
* `HasDetExpression p n`: `p` is the determinant of an `n × n` matrix whose entries are affine
  linear polynomials (Valiant's determinantal expression of size `n`). The determinantal
  complexity `dc(p)` is the least such `n`; statements use this predicate directly.
* `HasBorderDetExpression p n`: `p` is a limit (coefficientwise, over `ℂ`) of polynomials with
  a determinantal expression of size `n`. The border determinantal complexity is the least such
  `n`.
* `linSubst g f`: the polynomial `x ↦ f (g x)` for a square matrix `g`.
* `orbitClosure f`: the closure of `{x ↦ f (g x) | g invertible}` over `ℂ`.
* `paddedPerm R m n`: `x₀₀^(n+1-m) · perm_m` placed in the `(n+1) × (n+1)` grid of variables,
  the polynomial Mulmuley and Sohoni compare with `det_{n+1}`.
-/

namespace PEqualNP.Gct

open MvPolynomial

/-- The determinant of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def detPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

/-- The permanent of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def permPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).permanent

/-- `p` is the determinant of an `n × n` matrix whose entries are affine linear polynomials
(total degree at most one) in the variables of `p`. -/
def HasDetExpression {σ R : Type} [CommRing R] (p : MvPolynomial σ R) (n : ℕ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial σ R),
    (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = p

/-- `p` is a coefficientwise limit of complex polynomials that have a determinantal expression
of size `n`. For finitely many variables the polynomials involved have degree at most `n`, so
this is the limit in the usual topology of a finite-dimensional complex vector space. -/
def HasBorderDetExpression {σ : Type} (p : MvPolynomial σ ℂ) (n : ℕ) : Prop :=
  ∃ q : ℕ → MvPolynomial σ ℂ, (∀ k, HasDetExpression (q k) n) ∧
    ∀ s, Filter.Tendsto (fun k => (q k).coeff s) Filter.atTop (nhds (p.coeff s))

/-- Linear change of variables: the polynomial `x ↦ f (g x)`, which replaces each variable
`X i` by `∑ j, g i j * X j`. -/
noncomputable def linSubst {ι R : Type} [Fintype ι] [CommRing R] (g : Matrix ι ι R)
    (f : MvPolynomial ι R) : MvPolynomial ι R :=
  MvPolynomial.bind₁ (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) f

/-- The orbit closure of a complex polynomial under invertible linear changes of variables: the
coefficientwise limits of sequences `linSubst (g k) f` with every `g k` invertible. The orbit
lies in the finite-dimensional space of forms of the degree of `f` (when `f` is homogeneous),
where this is the closure in the usual topology, which for orbits of `GL` equals the Zariski
closure used in GCT. -/
def orbitClosure {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) :
    Set (MvPolynomial ι ℂ) :=
  {h | ∃ g : ℕ → Matrix.GeneralLinearGroup ι ℂ,
    ∀ s, Filter.Tendsto (fun k => (linSubst (g k : Matrix ι ι ℂ) f).coeff s) Filter.atTop
      (nhds (h.coeff s))}

/-- Where variable `(i, j)` of `perm_m` sits in the `(n + 1) × (n + 1)` grid: at
`(i + 1, j + 1)`. This is injective and avoids `(0, 0)` exactly when `m ≤ n`. -/
def padIndex (m n : ℕ) (p : Fin m × Fin m) : Fin (n + 1) × Fin (n + 1) :=
  (Fin.ofNat (n + 1) (p.1.val + 1), Fin.ofNat (n + 1) (p.2.val + 1))

/-- The padded permanent `x₀₀^(n+1-m) · perm_m`, homogeneous of degree `n + 1` in the
`(n + 1)²` variables of `det_{n+1}`. Meaningful when `m ≤ n`; statements assume it. -/
noncomputable def paddedPerm (R : Type) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
  MvPolynomial.X (0, 0) ^ (n + 1 - m) * MvPolynomial.rename (padIndex m n) (permPoly R m)

end PEqualNP.Gct

end Gct

section RiffleRank

/-!
# Riffle rank, in the case of two blocks

Riffle rank is a complexity measure for tensors introduced by B. Rossman (Riffle Rank, LAGOS
2025, Procedia Computer Science 273, Definition 3.1). Over a field `F`, a function
`f : [n]^(2k) → F` in the variables `(a₁, b₁, ..., a_k, b_k)` is riffle-basic if it is a product
`B(b₁, ..., b_k) * ∏ i, A_i(b₁, ..., b_(i-1), a_i)` of arbitrary `F`-valued factors, and the
riffle rank of `f` is the least number of riffle-basic functions with sum `f`.

This module states the case `k = 2` only, the one of Question C.1 of that paper: in the
variables `(a, b, c, d) = (a₁, b₁, a₂, b₂)` a riffle-basic function is
`A(a) * C(b, c) * D(b, d)`, with `A = A₁`, `C = A₂` and `D = B`.

The index set `[n]` is any type `X`; `Fin n` is the set of the source. The coefficients are any
type with the operations used, so a statement can be made over every field at once.

* `IsRiffleBasic f`: `f a b c d = A a * C b c * D b d` for some `A`, `C`, `D`.
* `RiffleRankLe r f`: `f` is a sum of `r` riffle-basic functions (so its riffle rank is at
  most `r`; summands may be zero, so the property is monotone in `r` over a ring).
* `pairId X F`: the function `[a = b] * [c = d]`, the tensor square of the identity matrix
  (`I_n ⊗ I_n` in the source, with `X = Fin n`).
-/

namespace PEqualNP.RiffleRank

/-- `f` is riffle-basic (two blocks): `f a b c d = A a * C b c * D b d` for some functions
`A` of `a`, `C` of `(b, c)` and `D` of `(b, d)`. -/
def IsRiffleBasic {X F : Type} [Mul F] (f : X → X → X → X → F) : Prop :=
  ∃ (A : X → F) (C D : X → X → F), ∀ a b c d : X, f a b c d = A a * C b c * D b d

/-- `f` is a sum of `r` riffle-basic functions: its riffle rank is at most `r`. -/
def RiffleRankLe {X F : Type} [Mul F] [AddCommMonoid F] (r : ℕ) (f : X → X → X → X → F) : Prop :=
  ∃ g : Fin r → X → X → X → X → F, (∀ i, IsRiffleBasic (g i)) ∧
    ∀ a b c d : X, f a b c d = ∑ i, g i a b c d

/-- The function `[a = b] * [c = d]`: one when `a = b` and `c = d`, zero otherwise. -/
def pairId (X F : Type) [DecidableEq X] [Zero F] [One F] : X → X → X → X → F :=
  fun a b c d => if a = b ∧ c = d then 1 else 0

end PEqualNP.RiffleRank

end RiffleRank
