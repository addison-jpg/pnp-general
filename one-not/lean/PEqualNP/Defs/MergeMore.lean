import Mathlib.Logic.Relation
import PEqualNP.Defs.LowMerge
import PEqualNP.Defs.Pebble
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs.Base
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENat.Lattice

section NewLowMerge

/-!
# Classes before a wire and new low merges at a line

The setting is that of `PEqualNP.Defs.LowMerge`: the root circuit model on the edge function of a
bipartite graph, `P` points then `L` lines (point `p` is input `p`, line `w` is input `P + w`),
incidence `inc : Fin P → Fin L → Bool`, wires numbered as in `Circuit.wires`.

Fix a line `w` and a wire index `g`. Take the points as vertices and, for every wire `j < g`
that is LOW for `w`, its ALIVE SET at `w` as a hyperedge. The CLASSES BEFORE `g` at `w` are the
connected components of this hypergraph (a point in no such alive set is alone). The wire `g` is
a NEW LOW MERGE at `w` when `g` is low for `w` and its alive set at `w` meets at least two classes
before `g` (the paper "the merge identity", section "Definitions": a gate low for `w` that joins
two or more classes when it appears, the classes following the order of the wires).

The classes are computed by a LABEL FOLD along the wires, the same labelling as the class labels
of the helper files of the checked inequality row (`lab` in the low-merge proof helpers): start
with label `p.val` on point `p`; at each wire `j`, if `j` is low for `w`, every point whose label
is a label of the alive set of `j` gets the largest such label. Two points are in the same class
before `g` exactly when their labels after the wires below `g` agree.

Names.
* `classStep P L inc C w lab j`: the labels after wire `j`, from the labels `lab` before it.
* `classLabel P L inc C g w : Fin P → ℕ`: the class labels before wire `g` (after wires `0` to
  `g - 1`).
* `SameClass P L inc C g w p q`: `p` and `q` have the same label before `g` (decidable).
* `AliveLinked P L inc C g w p q`: some wire `j < g` low for `w` has both `p` and `q` in its
  alive set at `w`. The connected components of the hypergraph are the classes of
  `Relation.EqvGen (AliveLinked P L inc C g w)`; `SameClass` agrees with that closure (a lemma,
  proved in the scratch file of this module, not built in).
* `classesMet P L inc C g w : Finset ℕ`: the labels of the classes before `g` met by the alive
  set of `g` at `w`.
* `IsNewLowMerge P L inc C g w`: `g` is low for `w` and `classesMet` has at least two elements.
  Decidable (instance below).

Caveats a statement must respect.
* The vertex set is ALL points (`Fin P`), not only the points of `w`. This changes nothing about
  the classes of points of `w`: the alive set of a wire low for `w` lies among the points of `w`
  (a lemma of the root, not built in), so a point off `w` is in no hyperedge and stays alone, and
  the alive set of a low `g` meets only classes of points of `w`.
* Every wire below `g` contributes, inputs included (as in the thinker's text: every wire `j`
  earlier than `g`). A point input on `w` has a one-point alive set and joins nothing; a line
  input other than `y_w` is low with an empty alive set; `y_w` is not low. So counting inputs or
  not gives the same classes.
* `g` itself need not be a gate, an OR gate or of fan-in two: the definition is semantic (low,
  alive set, classes). That an input wire is never a new low merge, and that a new low merge
  which is an OR of two earlier wires is a low merge (`PEqualNP.LowMerge.IsLowMerge`), are
  lemmas, not built in.
* AND/OR-only is NOT built in (`PEqualNP.CircuitLowerBounds.IsMonotoneCircuit` is the
  hypothesis), as for `IsLow`.
* The label values themselves carry no meaning beyond equality; only `SameClass` and the
  number of labels (`classesMet`) are meant to be stated on.
* Wires at or above the end of the circuit read `false`: they are low with an empty alive set,
  never new low merges.
-/

namespace PEqualNP.LowMerge

open PEqualNP.CircuitLowerBounds

/-- One step of the label fold: the labels after wire `j` from the labels `lab` before it. If
`j` is low for `w`, every point whose label is a label of the alive set of `j` at `w` gets the
largest label of that alive set; otherwise nothing changes. -/
def classStep (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)
    (lab : Fin P → ℕ) (j : ℕ) : Fin P → ℕ :=
  fun p =>
    if IsLow P L inc C j w ∧ lab p ∈ (aliveSet P L C j w).image lab then
      ((aliveSet P L C j w).image lab).sup id
    else lab p

/-- The class labels before wire `g` at line `w`: the fold of `classStep` along the wires
`0, 1, ..., g - 1`, starting from label `p.val` on point `p`. -/
def classLabel (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Fin P → ℕ :=
  (List.range g).foldl (classStep P L inc C w) (fun p => p.val)

/-- `p` and `q` are in the same class before wire `g` at line `w`. -/
def SameClass (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Prop :=
  classLabel P L inc C g w p = classLabel P L inc C g w q

/-- The hyperedge relation before `g`: some wire `j < g` low for `w` has both `p` and `q` in its
alive set at `w`. Its equivalence closure has the classes before `g` as its classes. -/
def AliveLinked (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Prop :=
  ∃ j < g, IsLow P L inc C j w ∧ p ∈ aliveSet P L C j w ∧ q ∈ aliveSet P L C j w

/-- The labels of the classes before `g` that the alive set of `g` at `w` meets. -/
def classesMet (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Finset ℕ :=
  (aliveSet P L C g w).image (classLabel P L inc C g w)

/-- NEW LOW MERGE: wire `g` is low for line `w` and its alive set at `w` meets at least two
classes before `g`. -/
def IsNewLowMerge (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Prop :=
  IsLow P L inc C g w ∧ 2 ≤ (classesMet P L inc C g w).card

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Decidable (SameClass P L inc C g w p q) := by
  unfold SameClass; infer_instance

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Decidable (IsNewLowMerge P L inc C g w) := by
  unfold IsNewLowMerge; infer_instance

end PEqualNP.LowMerge

end NewLowMerge

section PebbleThreeWay

/-!
# The three-way game on gate graphs

The three-way game (`routes/evasion/OBJECTS.md` DEF 3.1; `routes/evasion/DESK-GAPS.md` part 2,
block P2.0) on the gate graphs of `PEqualNP.Defs.Pebble`. This module records no result; it holds
only the definition a statement needs.

A gate is the three-element set `{v, p v, q v}` of a non-source `v` (`GateGraph.gate`). From a
kept set `R`, a three-way move places at most one vertex `u` not in `R`: `u` is a source (placed
freely), or some gate (of a non-source head) contains `u` and has its other two members in `R`.
So a value is recovered from a gate in any direction, as with a Latin-square operation: holding
`v` and `p v`, one may place `q v`, a backward move the black game forbids. One known member of a
gate is not enough.

* `GateGraph.ThreeWayMove R U`: a matching move (`GateGraph.MatchMove`) from the kept set `R`
  placing the set `U`, with at most one placed vertex. With one placed vertex `u` this says
  exactly: `u ∉ R`, and `u` is a source or lies in the gate of some non-source `h` with that
  gate inside `insert u R`. The empty placed set is a legal move (a pure removal, after `Step`
  has dropped vertices).

The three-way price is read through the generic play predicate of `PEqualNP.Defs.Pebble`:
`PriceLe G.ThreeWayMove x w` says some three-way play from the empty configuration reaches `x`
with every configuration of size at most `w`. No separate price function is defined.

Caveats a statement must respect:
* A configuration's size counts sources: a placed source costs a pebble like any other vertex.
* A step is "keep a subset, then place": `Step` keeps `R ⊆ P` and moves to `R ∪ U`. The
  thinker's "place, then drop any nodes" gives the same plays and the same peak sizes, since the
  configuration right after a placement is listed before the next step drops anything.
* The gate used to place `u` may be the gate of `u` itself (the forward, black direction) or the
  gate of a successor of `u` (the backward direction); its head must be a non-source.
* Because sources are placed freely, a backward move says something new only when the placed
  operand is itself a non-source.
-/

namespace PEqualNP.Pebble

namespace GateGraph

variable {n : ℕ} (G : GateGraph n)

/-- A three-way move from the kept set `R` placing the set `U`: a matching move
(`G.MatchMove R U`) that places at most one vertex. With `U = {u}` the matching sends `u` to the
head `h` of a gate that contains `u` and lies inside `R ∪ {u}`; when `u` is a source nothing is
required beyond `u ∉ R`. With `U = ∅` it is a pure removal. -/
def ThreeWayMove (R U : Finset (Fin n)) : Prop := G.MatchMove R U ∧ U.card ≤ 1

end GateGraph

end PEqualNP.Pebble

end PebbleThreeWay

section Peelable

/-!
# Peelable graphs

A finite simple graph on `Fin n` is PEELABLE if every induced subgraph with at least one edge has
a GOOD LEAF or a RUN of six. Both local shapes are the ones the last-gate line of the
meta-complexity work peels in its induction (a leaf step and a deep step), so a peelable graph is
one on which that induction never gets stuck.

* `delVerts G X`: the graph `G` with every edge that has an end in `X` deleted. The vertex type is
  kept (`Fin n`), so the vertices of `X` stay as isolated vertices. This is the induced subgraph on
  the complement of `X`, padded with isolated vertices.
* `GoodLeaf G`: a leaf `l` (its only neighbour is `p`) such that `p` has at most one neighbour
  besides `l`, or `p` has a second leaf `l' ≠ l`.
* `IsRun G a' a s t b b'`: six distinct vertices forming the path `a' - a - s - t - b - b'`, where
  `a, s, t, b` have exactly their two path neighbours as neighbours, and `a'` (resp. `b'`) has at
  most one neighbour besides `a` (resp. `b`). That one further neighbour may lie on the path (for
  example `a'` adjacent to `b'`, as in the 6-cycle).
* `HasPeel G`: if `G` has an edge, then `G` has a good leaf or a run.
* `Peelable G`: `HasPeel (delVerts G X)` for every vertex set `X`.

Caveats a statement must respect.

* The arity is fixed: an induced subgraph is `delVerts G X` on the same `Fin n`, never a graph on
  a smaller vertex type. Isolated vertices change neither `GoodLeaf` nor `IsRun`, so this is the
  same notion as quantifying over induced subgraphs `G.induce S`.
* In `IsRun`, the clause for an end counts EVERY neighbour other than its inner path neighbour,
  including a neighbour on the path. So "at most one neighbour off the path" is read as "at most
  one neighbour besides `a`" (resp. `b`): an end adjacent to the other end AND to a vertex off the
  path has two, and is not allowed.
* The good leaf and the run are the helper notions of the full-basis bound of the meta-complexity
  line, word for word (the run there is a structure with these six fields); they agree with these
  by a short proof, and that line's class hypotheses (closure under `delVerts`, and the dichotomy
  at every graph with an edge) hold for `Peelable`.
-/

namespace PEqualNP.Library.Peel

/-- The graph with every edge that has an end in `X` deleted, the vertex type kept. -/
def delVerts {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := G.Adj i j ∧ i ∉ X ∧ j ∉ X
  symm := ⟨fun _ _ h => ⟨G.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun i h => G.loopless.irrefl i h.1⟩

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Finset (Fin n)) :
    DecidableRel (delVerts G X).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj i j ∧ i ∉ X ∧ j ∉ X))

/-- A good leaf: a leaf `l` at `p` where `p` has at most one further neighbour, or a second leaf
`l'` at `p`. -/
def GoodLeaf {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨ (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Decidable (GoodLeaf G) :=
  inferInstanceAs (Decidable (∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
      (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))))

/-- A run of six: distinct vertices `a' - a - s - t - b - b'` where `a, s, t, b` have exactly the
two neighbours on the run, and `a'`, `b'` have at most one neighbour besides `a`, `b`. -/
def IsRun {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop :=
  [a', a, s, t, b, b'].Nodup ∧
    (∀ w, G.Adj a w ↔ w = a' ∨ w = s) ∧
    (∀ w, G.Adj s w ↔ w = a ∨ w = t) ∧
    (∀ w, G.Adj t w ↔ w = s ∨ w = b) ∧
    (∀ w, G.Adj b w ↔ w = t ∨ w = b') ∧
    (∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c) ∧
    (∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a' a s t b b' : Fin n) :
    Decidable (IsRun G a' a s t b b') :=
  inferInstanceAs (Decidable ([a', a, s, t, b, b'].Nodup ∧
    (∀ w, G.Adj a w ↔ w = a' ∨ w = s) ∧
    (∀ w, G.Adj s w ↔ w = a ∨ w = t) ∧
    (∀ w, G.Adj t w ↔ w = s ∨ w = b) ∧
    (∀ w, G.Adj b w ↔ w = t ∨ w = b') ∧
    (∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c) ∧
    (∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c)))

/-- The dichotomy at one graph: with an edge, a good leaf or a run. -/
def HasPeel {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∃ i j, G.Adj i j) → GoodLeaf G ∨ ∃ a' a s t b b' : Fin n, IsRun G a' a s t b b'

/-- A peelable graph: every induced subgraph (as `delVerts G X`) with an edge has a good leaf or a
run. -/
def Peelable {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ X : Finset (Fin n), HasPeel (delVerts G X)

end PEqualNP.Library.Peel

end Peelable

section Subdivision

/-!
# The 2k-fold subdivision of a graph on `Fin m`

For a graph `H` on `Fin m` and a number `k`, the subdivision replaces every edge of `H` by a path
of `2k + 1` edges through `2k` new vertices. It lives on `Fin (nS m k)`, `nS m k = m + 2k m^2`,
numbered without enumerating edges:

* the HUBS are the indices `0, .., m - 1` (the vertices of `H`, same index);
* a SLOT is a pair `(u, v)` of vertices of `H`; it is LIVE iff `u < v` and `H.Adj u v`; the slot
  `(u, v)` owns the `2k` indices `m + 2k (u m + v) + i`, `i < 2k`;
* the THREAD of a live slot is `u, m + 2k (u m + v), .., m + 2k (u m + v) + 2k - 1, v`, a path
  of `2k + 1` steps. The indices of a slot that is not live are isolated vertices.

With `k = 0` there are no new vertices and the subdivision is `H` itself.

The adjacency is `SimpleGraph.fromRel` of an explicit relation (arithmetic and bounded
existentials), so it is symmetric and irreflexive by construction and decidable when `H.Adj` is.

* `nS m k`: the number of vertices.
* `SubRel k H x y`: `x` then `y` are consecutive on the thread of a live slot, read upward.
* `subdiv k H`: the subdivision.
* `OnThr k H j`: `j` is an inner vertex of the thread of a live slot.
* `pos k H j`: the position `1 .. 2k` of `j` on its thread, `0` on hubs and dead slots.

The same definitions, with their first lemmas, were built for the meta-complexity line in a
helper module; they agree with these by `rfl`. Nothing here imports beyond the pinned library.
-/

namespace PEqualNP.Library.Subdivision

/-- The number of vertices of the subdivision: `m` hubs and `2k` indices for each of the `m * m`
slots. -/
def nS (m k : ℕ) : ℕ := m + 2 * k * m * m

/-- One step of a thread, read from the lower end `u` toward the upper end `v` of a live slot:
`x` is the vertex at position `p` and `y` the vertex at position `p + 1`, where position `0` is
the hub `u`, position `2k + 1` is the hub `v`, and position `t` with `1 ≤ t ≤ 2k` is the index
`m + 2k (u m + v) + (t - 1)`. -/
def SubRel {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)

/-- The 2k-fold subdivision of `H`: two indices are adjacent iff they are distinct and one thread
step joins them, in one of the two orders. -/
def subdiv {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin (nS m k)) :=
  SimpleGraph.fromRel (SubRel k H)

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (SubRel k H) :=
  fun x y => inferInstanceAs (Decidable (∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)))

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (subdiv k H).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x)))

/-- The index is an inner vertex of the thread of a live slot. -/
def OnThr {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (j : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidablePred (OnThr k H) :=
  fun j => inferInstanceAs (Decidable (∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val))

/-- The position of an index on its thread: `i + 1` on the inner vertex at offset `i` of a live
slot, `0` on hubs and on the indices of dead slots. -/
def pos {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (j : Fin (nS m k)) : ℕ :=
  if OnThr k H j then (j.val - m) % (2 * k) + 1 else 0

end PEqualNP.Library.Subdivision

end Subdivision

section TimeAlt

/-!
# Time classes up to constants, alternation in verifier form, and the fixed-pair link

Definitions for the conditional steps of the evasion chain. Read by the red team as drafts
(`reviews/attack-defs-2026-11-22.md`, last section) before they were placed here.

* `DTIMEO t`: deterministic time `K * t + K` for some `K` (no linear speedup is proved for the
  machine model, so classes are read up to constants).
* `NLIN a`: nondeterministic linear time in verifier form; the witness bound `a * |x|` is carried
  inside the relation.
* `Alt j s P`: `j` alternating blocks of length exactly `s`, the leading block existential.
  `Alt 0` is degenerate: use `j ≥ 1`.
* `SigmaV j T`: `j` alternations of blocks of length exactly `T |x|`, then a linear-time check.
* `Constructible T`: monotone, at least the identity, unary pad writable in time `c * T + c`.
* `HLint c`, `FP3 p q`: the hard link in integer-exponent form and its fixed-pair form at three
  alternations. These are HYPOTHESES of conditional statements; neither is proved.
* `rootUp v x`: the ceiling of the `v`-th root of `x`; `Coll u v`: nondeterministic linear time
  inside deterministic time of order `n^(u/v)`.
-/

namespace PEqualNP.Library

/-- D1. DTIME up to a constant factor and an additive constant. -/
def DTIMEO (t : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ K : ℕ, L ∈ DTIME (fun n => K * t n + K)}

/-- D2. Nondeterministic linear time in verifier form. The witness length bound `a * |x|` is
carried inside the relation (fix F7 of the route's note 210). -/
def NLIN (a : ℕ) : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair R (fun l => K * l + K) ∧
      (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ a * x.length) ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R}

/-- D3. `i` alternating blocks of length exactly `s`, the leading block existential. -/
def Alt : ℕ → ℕ → (List Bool → Prop) → Prop
  | 0, _, P => P []
  | i + 1, s, P => ∃ y : List Bool, y.length = s ∧ ¬ Alt i s (fun w => ¬ P (y ++ w))

/-- D4. Sigma_j time O(T) in verifier form: `j` blocks of length exactly `T |x|`, then a
linear-time check of the pair (input, all blocks). -/
def SigmaV (j : ℕ) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair R (fun l => K * l + K) ∧
      ∀ x : List Bool, x ∈ L ↔ Alt j (T x.length) (fun w => (x, w) ∈ R)}

/-- D5. Time-constructible, monotone, at least linear. -/
def Constructible (T : ℕ → ℕ) : Prop :=
  Monotone T ∧ (∀ n, n ≤ T n) ∧ ∃ c : ℕ,
    ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (T x.length) true) (fun n => c * T n + c)

/-- The hard link in integer-exponent form, for one collapse exponent `c`. -/
def HLint (c : ℕ) : Prop :=
  ∃ j p q : ℕ, 1 ≤ j ∧ 1 ≤ p ∧ c ^ j * p < q ∧
    ∀ L ∈ DTIMEO (fun m => 2 ^ (q * m)),
      ∃ K : ℕ, 1 ≤ K ∧ L ∈ SigmaV j (fun m => K * 2 ^ (p * m) + K)

/-- The fixed-pair link at three alternations, all languages: deterministic time `2^(q m)` up to
constants is inside three-alternation time `O(2^(p m))`. -/
def FP3 (p q : ℕ) : Prop :=
  ∀ L ∈ DTIMEO (fun m => 2 ^ (q * m)),
    ∃ K : ℕ, 1 ≤ K ∧ L ∈ SigmaV 3 (fun m => K * 2 ^ (p * m) + K)

/-- The least `r` with `x ≤ r ^ v`: the ceiling of the `v`-th root of `x` (for `v ≥ 1`). -/
noncomputable def rootUp (v x : ℕ) : ℕ := sInf {r : ℕ | x ≤ r ^ v}

/-- The collapse hypothesis at the rational exponent `u / v`: nondeterministic linear time inside
deterministic time `O(ceil (n^(u/v)))`. -/
def Coll (u v : ℕ) : Prop :=
  ∀ a : ℕ, NLIN a ⊆ DTIMEO (fun n => rootUp v (n ^ u))

end PEqualNP.Library

end TimeAlt

section CoLevel

/-!
# Co-level of a multiset of p-units

Fix a field `K`, a number `m` of variables `y_0, .., y_(m-1)` (the polynomial ring
`MvPolynomial (Fin m) K`) and a number `p` of rows.

A linear form is `l(y) = c_0 y_0 + .. + c_(m-1) y_(m-1)`, given by its coefficient vector
`c : Fin m → K`. Linear forms here are HOMOGENEOUS: no constant term. So every factor
`1 + l(y)` has constant term `1`, and every p-unit has constant term `1`.

A p-unit is `U = (1 + l_0(y)) * .. * (1 + l_(p-1)(y))`, given by its `p × m` coefficient
matrix `c : Fin p → Fin m → K` (row `r` is the form `l_r`). Two different matrices may give
the same polynomial (rows permuted); no notion below depends on which matrix is used.

The co-level of a finite multiset `A` of p-units is the least `N` such that there are p-units
`U_1, .., U_N` with `sum_(U in A) U + U_1 + .. + U_N = |A| + N` as polynomials (the constant
polynomial `|A| + N`), and `⊤` if no such `N` exists.

* `linForm c`: the linear form `sum_i c_i y_i`.
* `pUnit c`: the p-unit `prod_r (1 + linForm (c r))` of the coefficient matrix `c`.
* `CoLevelWitness A N`: there are `N` p-units completing the sum of `A` to the constant `|A| + N`.
* `coLevel A : ℕ∞`: the least `N` with `CoLevelWitness A N`, `⊤` if none.

Caveats a statement must respect.

* A multiset of p-units is a `Multiset (Fin p → Fin m → K)` of coefficient matrices; its
  polynomials are `A.map pUnit`. `|A|` is `Multiset.card A`, counted with multiplicity.
* The target constant is the literal `|A| + N`, cast into the polynomial ring (in
  characteristic `l` it is read mod `l`). Since every p-unit has constant term `1`, "the sum is
  a constant" and "the sum equals `|A| + N`" say the same thing.
* `coLevel` is an `ℕ∞` defined by `sInf` over the naturals that admit a witness; `sInf ∅ = ⊤`.
* `p = 0` makes every p-unit the polynomial `1`, so every multiset has co-level `0`; likewise
  `m = 0` (no variables) makes every linear form `0` and every multiset has co-level `0`.
* The field `K` is arbitrary. Values computed in the source are for the complex numbers and a
  generic unit; over a small field they can differ (over the field with three elements some single
  p-units have co-level 2). A statement must name its field.
-/

namespace PEqualNP.CoLevel

open MvPolynomial

variable {K : Type*} [Field K] {m p : ℕ}

/-- The homogeneous linear form `sum_i c_i y_i` with coefficient vector `c`. -/
noncomputable def linForm (c : Fin m → K) : MvPolynomial (Fin m) K :=
  ∑ i, C (c i) * X i

/-- The p-unit `prod_r (1 + l_r(y))` whose row `r` is the linear form with coefficients `c r`.
The number of rows `p` is the length of the product. -/
noncomputable def pUnit (c : Fin p → Fin m → K) : MvPolynomial (Fin m) K :=
  ∏ r, (1 + linForm (c r))

/-- `N` p-units `U_1, .., U_N` complete the multiset `A` of p-units: the sum of `A` plus
`U_1 + .. + U_N` is the constant polynomial `|A| + N`. -/
def CoLevelWitness (A : Multiset (Fin p → Fin m → K)) (N : ℕ) : Prop :=
  ∃ B : Fin N → Fin p → Fin m → K,
    (A.map pUnit).sum + ∑ j, pUnit (B j) = ((Multiset.card A + N : ℕ) : MvPolynomial (Fin m) K)

/-- The co-level of a multiset of p-units: the least `N` with `CoLevelWitness A N`, and `⊤`
if there is none. -/
noncomputable def coLevel (A : Multiset (Fin p → Fin m → K)) : ℕ∞ :=
  sInf ((fun N : ℕ => (N : ℕ∞)) '' {N | CoLevelWitness A N})

end PEqualNP.CoLevel

end CoLevel
