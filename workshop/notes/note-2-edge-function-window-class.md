# Note 2: the edge-function bound on the window class

pequalnp.com, 2026-11-24. An addendum to Note 1. Every statement below is checked by the project's
checker setup (Lean 4, the pinned Mathlib, only `propext`, `Classical.choice`, `Quot.sound`); no
claim is made about whether it is known.

## 1. The class

Call a vertex a *hub* if it has at least three neighbours. A graph G is in the **window class W6**
when every cycle of G has length at least 6 and contains six cyclically consecutive vertices, each
with at most two neighbours in G (a *window*).

Lean: `PEqualNP.MetaComplexity.EdgeFn.Window.W6` in
`lean/PEqualNP/MetaComplexity/Helpers/EdgeFnWindow.lean`.

W6 contains:
- every forest (no cycles; `forest_w6`);
- every graph of the class of L-meta-204 (every cycle of length at least 7, distinct hubs joined
  only by walks of length at least 7; `t7_w6`);
- hence the classes of L-meta-113 and L-meta-115 (cycles at least 9);
- graphs that none of those contain, for example the 8-cycle with one pendant leaf at each of two
  ADJACENT cycle vertices (hubs at distance 1), or two long cycles joined by an edge.

## 2. Statements (checked)

For G in W6, A a set of vertices that no edge meets, f = OR over a in A of x_a, OR, over edges uv,
of (x_u AND x_v); circuits of fan-in two over AND, OR, NOT, every gate counted:

(a) `w6_lb`: every circuit for f has at least |A| + |E| + tau(G) - 1 gates.
    This contains L-meta-204 and the forest bound L-meta-104 (there with A empty).
(b) `w6_exact`: if G has an edge, the least circuit size of the edge function f_G is exactly
    |E| + tau(G) - 1 (upper bound from the monotone construction of L-meta-154).
(c) `w6_mono`: every monotone fan-in-two circuit for f_G has at least |E| + tau(G) - 1 gates (the
    form of L-meta-115, there under cycles of length at least 9).
(d) `w6_not_free`: every circuit for f_G has an equivalent circuit with no NOT gate and no more
    gates (the form of L-meta-113, there under cycles and hub distance at least 9).

## 3. Why the class is W6

The induction of L-meta-204 (`a1_of_pieces` in `EdgeFnGraphPlan.lean`) already holds for ANY
class closed under vertex deletion in which every graph with an edge has a good leaf or a run (six
distinct vertices a'-a-s-t-b-b', the inner four with exactly their two run neighbours, a' and b'
with at most two neighbours). The numerals 7 entered only through the graph lemma that finds a run.
For W6 that lemma is short:
- an acyclic graph with an edge has a good leaf (`Forest.forest_good_leaf`);
- otherwise any cycle has a window, and a window IS a run (`run_of_window`).
W6 is closed under vertex deletion: a cycle of a vertex-deleted graph is a cycle of G with the same
vertices, and degrees only drop (`w6_hered`).

## 4. Beyond W6: the window-of-four class W4 (maximum degree 3)

Row L-meta-658 (the run-of-four bound) is stated with the statement of row L-meta-568 (the
free-input chain law) as its hypothesis, and L-meta-568 is proved in
`lean/PEqualNP/Outside/L_meta_568.lean`. So the run-of-four bound holds without hypothesis: the
term `L658 L_meta_568` is checked.

Call G a member of **W4** when every cycle has length at least 5 and contains four cyclically
consecutive vertices with at most two neighbours each. A window of four is a run of four in the
sense of L-meta-658, so (`EdgeFnWindow4.lean`):

(e) `w4_lb`: for G of maximum degree 3 in W4, every circuit for f has at least |A| + |E| + tau - 1
    gates.
(f) `w4_exact`: the same graphs with an edge have exact size |E| + tau - 1.

W4 contains W6 (`w6_w4`). With maximum degree 3, W4 also contains the 5-cycle with a pendant leaf
and the 6-cycle with a pendant leaf. Note 1 gives the 6-cycle with a pendant leaf as a smallest
graph where the proof of L-meta-204 does not apply.

## 5. A 4-cycle always saves a gate (checked)

(g) `c4_upper` (`EdgeFnC4.lean`): if G contains a 4-cycle a-b-c-d (as a subgraph, not
    necessarily induced) and T is any vertex cover, then f_G has a circuit with |E| + |T| - 2
    gates. A cover of the 4-cycle contains an opposite pair, say a and c. The circuit computes
    z = x_b OR x_d once and uses it at both a and c. Formally, the edges ab, ad, cb, cd become
    az, cz on one more input, and `plug` (from L-meta-548) substitutes z.
(h) `c4_free_of_exact`: so if |E| + tau - 1 is a lower bound for G, then G has no 4-cycle.

## 6. Computation: every small graph (exact SAT synthesis)

Exact synthesis by SAT (basis AND, OR of fan-in two, and NOT, every gate counted, the same cost
measure as `HasCircuitSize`). The encoder was validated on P2, P3, K3, C4, C5 and P5 against the
checked values. This is computation, NOT a checked statement.

- Every graph with at most 6 vertices and no isolated vertex was run: 115 graphs, 87 finished
  before the run was stopped. The 28 not finished all contain a 4-cycle, a side that (g) now
  settles. The C4-free graph with atlas index 130 was not run. Among the 87, the size is
  |E| + tau - 1 exactly when G has no 4-cycle: 42 C4-free graphs, all exact; 45 graphs with a
  4-cycle, all strictly below. The C4-free graphs include triangles, the 5-cycle, and graphs
  outside W4 and W6.
- Graphs on 7 vertices that have no 4-cycle (73 graphs): the run is in progress. At least 25 are finished, all exact, with no counterexample.

**Conjecture.** For every graph G with an edge, the least circuit size of f_G is |E| + tau(G) - 1
if and only if G has no 4-cycle as a subgraph. The direction "only if" is (h). The direction "if"
is checked on W6, and on W4 with maximum degree 3. For all graphs with at most 6 vertices it is
supported by computation (one graph, atlas index 130, not yet run). Compare the K_(2,2)-free
condition (K_(2,2) is the 4-cycle) in the single-level monotone bound of Amano and Maruoka quoted
in Note 1.

## 7. How far these proofs go, and what is open

- Within the current notion of a run, W6 is close to the largest class this proof reaches: a cycle
  with no window, kept with one pendant leaf at each of its hubs, has neither a good leaf nor a run.
- Cycles of length 3 to 5 are outside W6. The 4-cycle is a counterexample to the bound (Note 1).
  The 5-cycle satisfies it (L-meta-106) but has no run. The triangle (majority of three) is not covered by W6.
- Example outside W6 where the bound is NOT known: the theta graph of three paths of length 4
  between two hubs (11 vertices, 12 edges, tau = 5, predicted size 16). It has no good leaf and no
  run. A proof for it needs a "run of four" step with arbitrary outer vertices; the project's
  RunAsm files (row L-meta-658) attack that step.
