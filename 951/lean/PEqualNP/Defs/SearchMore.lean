import PEqualNP.Defs.SearchQ
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice.Fold
import PEqualNP.Defs.Search

section SearchCP

/-!
# Definitions of the P = NP algorithm search: cutting planes and triangle dags

Cutting planes over the integers (Cook, Coullard and Turan 1987) for CNFs on `V`. A line is
an inequality `∑ a_v x_v ≥ c` with integer coefficients over 0/1 variables. Rules: an axiom
(a clause read as the sum of its literals `≥ 1`, literal `x` or `1 - x`); the Boolean axioms
`x_v ≥ 0` and `-x_v ≥ -1`; the sum of two earlier lines; an earlier line times a nonnegative
integer; an earlier line divided by a positive integer `d` dividing all its coefficients, the
constant rounded up. A refutation contains `0 ≥ 1`. Its size here is its number of lines.

Triangles for a split (Hrubes and Pudlak 2017; Sokolov 2017; Beame and Whitmeyer 2025): a set
`{x | a x < b x}` with `a` reading only the first player's coordinates and `b` only the
second's. Integer labels: on a finite cube real labels give the same sets.
-/

namespace PEqualNP.Search

/-- A cutting planes line `∑ v, e.1 v * x v ≥ e.2`: coefficients and constant. -/
abbrev CPLine (V : Type) : Type := (V → ℤ) × ℤ

/-- The 0/1 point `a` satisfies the line `e`. -/
def CPLine.Holds {V : Type} [Fintype V] (a : V → Bool) (e : CPLine V) : Prop :=
  e.2 ≤ ∑ v, e.1 v * (if a v then 1 else 0)

/-- The line of a clause: the sum over its literals of `x_v` for `(v, true)` and `1 - x_v` for
`(v, false)`, at least `1`. -/
def clauseCP {V : Type} [DecidableEq V] (C : PEqualNP.ProofComplexity.Clause V) : CPLine V :=
  (fun v => ∑ l ∈ C, if l.1 = v then (if l.2 then 1 else -1) else 0,
   1 - ∑ l ∈ C, if l.2 then 0 else 1)

/-- `IsCPDerivation F π`: the list `π` of lines is a cutting planes derivation from the
clauses `F`, written NEWEST LINE FIRST. -/
inductive IsCPDerivation {V : Type} [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : List (CPLine V) → Prop
  | nil : IsCPDerivation F []
  | ax {π : List (CPLine V)} (C : PEqualNP.ProofComplexity.Clause V) :
      IsCPDerivation F π → C ∈ F → IsCPDerivation F (clauseCP C :: π)
  | boolLo {π : List (CPLine V)} (v : V) :
      IsCPDerivation F π → IsCPDerivation F ((fun u => if u = v then 1 else 0, 0) :: π)
  | boolHi {π : List (CPLine V)} (v : V) :
      IsCPDerivation F π → IsCPDerivation F ((fun u => if u = v then -1 else 0, -1) :: π)
  | add {π : List (CPLine V)} {e e' : CPLine V} :
      IsCPDerivation F π → e ∈ π → e' ∈ π → IsCPDerivation F ((e.1 + e'.1, e.2 + e'.2) :: π)
  | mul {π : List (CPLine V)} {e : CPLine V} (k : ℕ) :
      IsCPDerivation F π → e ∈ π → IsCPDerivation F (((k : ℤ) • e.1, (k : ℤ) * e.2) :: π)
  | div {π : List (CPLine V)} {e : CPLine V} (d : ℕ) :
      IsCPDerivation F π → e ∈ π → 0 < d → (∀ v, (d : ℤ) ∣ e.1 v) →
      IsCPDerivation F ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) :: π)

/-- A cutting planes refutation: a derivation containing `0 ≥ 1`. Its size is `π.length`. -/
def IsCPRefutation {V : Type} [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (CPLine V)) : Prop :=
  IsCPDerivation F π ∧ ((0 : V → ℤ), (1 : ℤ)) ∈ π

/-! ## Triangle dags -/

/-- `S` is a triangle for the split `side`: `S = {x | a x < b x}` where `a` reads only the
coordinates with `side v = true` and `b` only the others. -/
def IsTri {V : Type} (side : V → Bool) (S : Set (V → Bool)) : Prop :=
  ∃ a b : (V → Bool) → ℤ, (∀ x y, a (mix side x y) = a x) ∧ (∀ x y, b (mix side x y) = b y) ∧
    ∀ x, x ∈ S ↔ a x < b x

/-- `IsTriDag side F ρ`: `IsRectDag` with triangles in place of rectangles. -/
inductive IsTriDag {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V)) :
    List (Set (V → Bool)) → Prop
  | nil : IsTriDag side F []
  | sink {ρ : List (Set (V → Bool))} {R : Set (V → Bool)} :
      IsTriDag side F ρ → IsTri side R →
      (∃ C ∈ F, ∀ a ∈ R, ¬ PEqualNP.ProofComplexity.ClauseSat a C) → IsTriDag side F (R :: ρ)
  | split {ρ : List (Set (V → Bool))} {R R₁ R₂ : Set (V → Bool)} :
      IsTriDag side F ρ → IsTri side R → R₁ ∈ ρ → R₂ ∈ ρ → R ⊆ R₁ ∪ R₂ →
      IsTriDag side F (R :: ρ)

/-- A triangle dag that solves the search problem of `F`. Its size is its length. -/
def IsTriDagFor {V : Type} (side : V → Bool) (F : Set (PEqualNP.ProofComplexity.Clause V))
    (ρ : List (Set (V → Bool))) : Prop :=
  IsTriDag side F ρ ∧ Set.univ ∈ ρ

end PEqualNP.Search

end SearchCP

section SearchQSyn

/-!
# Definitions of the P = NP algorithm search: Res(lin) over the integers with syntactic rules

The system R(lin) of Raz and Tzameret (Ann. Pure Appl. Logic 155, 2008) with only syntactic
rules. The semantic one-line weakening of `IsResLinQDerivation` makes every tautology one step
from any axiom, and over the integers some counting principles are short tautologies (the
refutation of L-alg-004), so size lower bounds for pigeonhole-type formulas are false there.
Here a line may only grow by adding equations, the equations `0 = c` with `c ≠ 0` may be
dropped, and the Boolean axioms `x = 0 ∨ x = 1` are given.
-/

namespace PEqualNP.Search

/-- `IsResLinQSynDerivation F π`: the list `π` of lines is an R(lin) derivation from the
clauses `F` with syntactic rules, NEWEST LINE FIRST. Rules: an axiom (exactly the equations of
the literals of a clause of `F`); the Boolean axiom `v = 0 ∨ v = 1`; resolution as in
`IsResLinQDerivation` (an integer combination of the first equations of two earlier lines,
followed by the rest of both); weakening (any line containing every equation of an earlier
line); simplification (an earlier line with its equations of the form `0 = c`, `c ≠ 0`,
removed). -/
inductive IsResLinQSynDerivation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : List (QLine V) → Prop
  | nil : IsResLinQSynDerivation F []
  | ax {π : List (QLine V)} {L : QLine V} (C : PEqualNP.ProofComplexity.Clause V) :
      IsResLinQSynDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) →
      IsResLinQSynDerivation F (L :: π)
  | bool {π : List (QLine V)} (v : V) :
      IsResLinQSynDerivation F π →
      IsResLinQSynDerivation F ([litQEq (v, false), litQEq (v, true)] :: π)
  | res {π : List (QLine V)} {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      IsResLinQSynDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π →
      IsResLinQSynDerivation F (((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) :: π)
  | weaken {π : List (QLine V)} {C D : QLine V} :
      IsResLinQSynDerivation F π → C ∈ π → (∀ e ∈ C, e ∈ D) →
      IsResLinQSynDerivation F (D :: π)
  | simp {π : List (QLine V)} {C : QLine V} :
      IsResLinQSynDerivation F π → C ∈ π →
      IsResLinQSynDerivation F (C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) :: π)

/-- A syntactic R(lin) refutation: a derivation containing the empty line. -/
def IsResLinQSynRefutation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (QLine V)) : Prop :=
  IsResLinQSynDerivation F π ∧ ([] : QLine V) ∈ π

end PEqualNP.Search

end SearchQSyn

section SearchQTree

/-!
# Definitions of the P = NP algorithm search: tree-like Res(lin) over the integers

A tree-like derivation of a line: every node is derived from its own children, never from a
shared line, so a line used twice is derived twice. The rules are those of
`IsResLinQDerivation` (axiom, resolution on the first equations, semantic weakening from one
line). The size counts nodes, that is lines, so a lower bound on it is a lower bound on the
number of lines of a tree-like refutation (and on its bit size).
-/

namespace PEqualNP.Search

/-- A tree-like Res(lin) derivation over the integers of the line `L` from the clauses `F`. -/
inductive ResLinQTree {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : QLine V → Type
  | ax {L : QLine V} (C : PEqualNP.ProofComplexity.Clause V) :
      C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) → ResLinQTree F L
  | res {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      ResLinQTree F (e :: C) → ResLinQTree F (e' :: D) →
      ResLinQTree F ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D))
  | weaken {C D : QLine V} :
      ResLinQTree F C → (∀ a : V → Bool, QLine.Holds a C → QLine.Holds a D) →
      ResLinQTree F D

/-- The number of nodes (lines) of a tree-like derivation. -/
def ResLinQTree.size {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.Clause V)} : {L : QLine V} → ResLinQTree F L → ℕ
  | _, .ax _ _ _ => 1
  | _, .res _ _ t t' => t.size + t'.size + 1
  | _, .weaken t _ => t.size + 1

end PEqualNP.Search

end SearchQTree

section CoverPromise

/-!
# Definitions of the promise vertex cover reduction

The objects of the reduction from CNF satisfiability to promise vertex cover, stated over the
CNF formulas of `Defs/Search.lean`.

* The textbook graph of a CNF formula: two literal vertices for every variable that occurs,
  joined by an edge; a vertex for every occurrence of a literal in a clause, with a clique on
  the occurrences of each clause; and each occurrence joined to its literal.
* A vertex cover: a finite set of vertices meeting every edge.
* The reduction: append a fresh positive literal `y` to every clause and add the unit clause
  `¬y`; the graph is the textbook graph of the new formula.
* The cover: the one read off the all-true assignment (the literal "true" of every variable,
  and every occurrence except the first true one in its clause).
-/

namespace PEqualNP.MetaComplexity.CoverPromise

open PEqualNP.Search

/-- The vertices: a literal `(x, b)`, or an occurrence `(i, j)`, the `j`-th literal of the
`i`-th clause (both counted from `0`). Only finitely many of them carry edges in the graphs below;
the others are isolated and play no role for vertex covers. -/
abbrev Vertex : Type := Literal ⊕ (ℕ × ℕ)

/-- The variables that occur in a formula. -/
def vars (ψ : CNF) : Finset ℕ :=
  (ψ.flatMap (List.map Prod.fst)).toFinset

/-- The `i`-th clause of a formula, the empty clause past its end. -/
def clauseAt (ψ : CNF) (i : ℕ) : Clause :=
  ψ.getD i []

/-- Adjacency of the textbook graph of a formula `ψ`: the two literals of an occurring
variable; two distinct occurrences of the same clause; an occurrence and its literal. -/
def satAdj (ψ : CNF) : Vertex → Vertex → Prop
  | .inl a, .inl b => a.1 = b.1 ∧ a.2 ≠ b.2 ∧ a.1 ∈ vars ψ
  | .inr (i, j), .inr (k, l) =>
      i = k ∧ j ≠ l ∧ j < (clauseAt ψ i).length ∧ l < (clauseAt ψ i).length
  | .inr (i, j), .inl a => (clauseAt ψ i)[j]? = some a
  | .inl a, .inr (i, j) => (clauseAt ψ i)[j]? = some a

/-- The textbook graph of a formula `ψ` (reduction from CNF satisfiability to vertex
cover). -/
def satGraph (ψ : CNF) : SimpleGraph Vertex where
  Adj := satAdj ψ
  symm := ⟨by
    rintro (⟨x, a⟩ | ⟨i, j⟩) (⟨y, b⟩ | ⟨k, l⟩) h <;> simp only [satAdj] at h ⊢
    · exact ⟨h.1.symm, h.2.1.symm, h.1 ▸ h.2.2⟩
    · exact h
    · exact h
    · obtain ⟨rfl, h1, h2, h3⟩ := h
      exact ⟨rfl, Ne.symm h1, h3, h2⟩⟩
  loopless := ⟨by
    rintro (⟨x, a⟩ | ⟨i, j⟩) h <;> simp [satAdj] at h⟩

/-- A vertex cover: a finite set of vertices meeting every edge. -/
def IsVertexCover {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

/-- The cover read off an assignment `σ`: the literal `(x, σ x)` of every occurring
variable, and every occurrence except the first one that is true under `σ` in its clause
(`List.findIdx` is the length of the clause when no literal of it is true). -/
def coverOf (ψ : CNF) (σ : Assignment) : Finset Vertex :=
  ((vars ψ).image fun x => (x, σ x)).disjSum
    ((Finset.range ψ.length).biUnion fun i =>
      ((Finset.range (clauseAt ψ i).length).filter
        (fun j => j ≠ (clauseAt ψ i).findIdx (Literal.eval σ))).image fun j => (i, j))

/-- A variable that does not occur in `φ`: one more than the largest that does. -/
def fresh (φ : CNF) : ℕ :=
  (vars φ).sup id + 1

/-- `φ' = {C ∨ y : C ∈ φ} ∪ {¬y}` with `y = fresh φ`. -/
def cvcFormula (φ : CNF) : CNF :=
  φ.map (fun C => C ++ [(fresh φ, true)]) ++ [[(fresh φ, false)]]

/-- The graph of the reduction: the textbook graph of `φ'`. -/
def cvcGraph (φ : CNF) : SimpleGraph Vertex :=
  satGraph (cvcFormula φ)

/-- The cover of the reduction: the cover of the textbook graph of `φ'` read off the
assignment "every variable true" (which falsifies exactly the clause `¬y` of `φ'`). -/
def cvcCover (φ : CNF) : Finset Vertex :=
  coverOf (cvcFormula φ) (fun _ => true)

end PEqualNP.MetaComplexity.CoverPromise

end CoverPromise
