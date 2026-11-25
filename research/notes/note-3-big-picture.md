# Note 3: big picture: the edge function, OR circuits, and where the method stops

2026-11-24. Every statement marked (checked) is checked with only `propext`, `Classical.choice`
and `Quot.sound`. Everything else is an argument in prose, NOT a checked statement.

## 1. Two sides of one quantity

For a graph G with vertex cover T, write each edge as (t, v) with t in T, and let S_t be the
neighbours assigned to t. Then

    C(f_G)  <=  2|T| - 1  +  OR(S_t : t in T),

where OR(S) is the least number of fan-in-two OR gates that compute ALL the disjunctions
OR_{v in S_t} x_v at once (sharing allowed). Computing each disjunction separately costs
sum (|S_t| - 1) = |E| - |T|, which gives L-meta-105: C(f_G) <= |E| + |T| - 1.

Checked pieces of the upper side:
- `biclique_upper` (`EdgeFnBiclique.lean`), all sizes variable: if P is a subset of T and B is
  disjoint from P, with P x B a set of edges (a copy of K_{p,b}), then
  C(f_G) + 1 + (p - 1)(b - 1) <= |E| + |T|. This is one shared OR of B, read p times.
- `biclique_family_upper` (`EdgeFnBicliqueFamily.lean`): for any list of bicliques (P_i, B_i)
  with each P_i inside T and edge sets pairwise disjoint, C(f_G) + 1 + sum_i (|P_i| - 1)(|B_i| - 1)
  <= |E| + |T|. A biclique-cover upper bound, the OR-sharing side of section 1 made explicit.
- `c4_upper`, `c4_free_of_exact` (`EdgeFnC4.lean`): the case p = b = 2. So exactness of
  |E| + tau - 1 forces G to have no 4-cycle.

Checked pieces of the lower side, |E| + tau - 1 <= C(f_G):
- `w6_lb`, `w6_exact`, `w6_mono`, `w6_not_free` (`EdgeFnWindow.lean`), on the hereditary class
  W6: every cycle has length at least 6 and six consecutive vertices of degree at most 2.
- `w4_lb`, `w4_exact` (`EdgeFnWindow4.lean`), on W4 with maximum degree 3. Here L-meta-658 is
  used unconditionally: its hypothesis is the checked row L-meta-568.

## 2. The barrier (prose)

When no two of the S_t share two elements (no K_{2,2} between T and the rest), the classical
result on OR (rectifier) circuits for (2,2)-free Boolean matrices (Nechiporuk; recalled, not
re-opened here) gives
OR(S_t) = sum (|S_t| - 1). So on C4-free graphs the upper side above is exactly
|E| + tau - 1. The natural conjecture is then

    C4-free  ==>  C(f_G) = |E| + tau(G) - 1.

That conjecture CANNOT be proved by this project's method, and it is probably false for dense
graphs, for this reason. Take the point-line incidence graph of a projective plane of order q:
it is bipartite, C4-free and explicit, with n = 2(q^2 + q + 1) vertices and
|E| = Theta(n^{3/2}) edges. The conjecture would give C(f_G) = Omega(n^{3/2}) for an explicit
function in P, against general circuits with NOT gates. The best known lower bound for any
explicit function is about 3.1 n. So the conjecture on dense C4-free graphs would be a major
breakthrough.

The checked classes W6 and W4 are sparse: every cycle needs its own run of degree-2 vertices,
so |E| <= c n for an absolute constant c. Gate elimination by good leaves and runs pays a constant number of gates
per eliminated vertex, which is linear in n. So the lower side of this program is LINEAR by
construction, and the reach of these methods is a density question:

- Linear |E| (sparse, long threads): exact values, checked (W6, W4).
- |E| = n^{1+eps}, C4-free: the exact value would give superlinear circuit lower bounds. Open,
  and beyond the known techniques.
- Graphs with large K_{p,b}: the value is strictly below |E| + tau - 1 (checked, biclique_upper).
  The right quantity is the OR-circuit complexity of the cover's neighbourhood matrix.

## 3. Elsewhere in the repository: constants replaced by variables (checked)

- `sat_ratio` (`CircuitLowerBounds/Helpers/SatRatio.lean`): for all a, b with 4a < 5b, no size
  bound b * s(n) <= a * n + c puts SAT in SIZE s. L-clb-040 is the case a/b = 99/100. The source
  is L-clb-041 (length 4k + 2 needs 5k + 1 gates).
- `graphPHP_no_pc_general` (`ProofComplexity/Helpers/GraphPHPGeneral.lean`): on any
  (s, delta) boundary expander with delta >= 2 and s >= 1, the graph pigeonhole CNF has no
  polynomial calculus refutation over F2 of degree D for every D <= s. L-pcx-046 has delta = 2
  and asks for 2(D + 1) <= s.

## 4. More constants made variable (checked)

- `linear_sets_lb` (`MetaComplexity/Helpers/LinearSetsLB.lean`): m sets of points, pairwise
  meeting in at most one point, each with more than k points. Every fan-in-two AND/OR circuit
  that computes their ORs on inputs of weight at most k has at least k * m gates. L-meta-275 is
  the case n = 7, m = 4, k = 2.
- `path_gadget_upper` (`MetaComplexity/Helpers/PathGadgetUpper.lean`): L-meta-572 for every N, h,
  u, v and g, without its five hypotheses, which the proof never used.
- `pendant_edge_general` (`MetaComplexity/Helpers/PendantEdgeGeneral.lean`): L-meta-538 for every
  graph with a pendant edge. The hypothesis that the graph embeds in a k-subdivision is dropped.
- `lin_indep_of_eval_perm` (`Library/Helpers/PermMatrixField.lean`): L-lib-130 over any field,
  characteristic 2 included. The row is stated over the rationals.
- `lin_refutation_len`, `php_lin_len` (`ProofComplexity/Helpers/LinRefutationLen.lean`): every
  Res(+) refutation of any CNF without the empty clause has at least two lines, so every
  PHP m n with n >= 1. L-pcx-016 is PHP 2 1.
- `funPHP_one_hole` (`ProofComplexity/Helpers/FunPHPOneHole.lean`): the functional pigeonhole
  system with m >= 2 pigeons and one hole has a polynomial calculus refutation of degree 2.
  L-pcx-040 is m = 2.

- `PermIsotropicGeneral.main` (`Gct/Helpers/PermIsotropicGeneral.lean`): for every n >= 2, a
  subspace W of complex n x n matrices with perm(J + t) = n! for all t in W has
  2 dim W <= n^2. L-gct-055 is n = 3 (dim <= 4). The Hessian of perm at J is (n-2)! on positions
  in different rows and columns, and 0 elsewhere. Vanishing along every line J + s t makes W totally
  isotropic for that form, and the form is nondegenerate for n >= 2.

- `cross_refutation` (`ProofComplexity/Helpers/CrossGeneral.lean`): for all a, b >= 1, the a x b
  cross formula (OR of x_i, OR of y_j, and NOT x_i OR NOT y_j for all i, j) has a Res(b, +)
  refutation (termwise weakening, as in L066) with at most 2ab + 3 lines. L-pcx-066 is a = b = 2
  (11 lines). Open: the width here is b; whether width 2 suffices for every a, b is not settled.

- `funPHP_upper` (`ProofComplexity/Helpers/FunPHPUpper.lean`): for all m > N, the functional
  pigeonhole system has a polynomial calculus refutation over F2 of degree N + 1. With L027 (no
  refutation of degree B when 2B <= N + 1), the least degree lies in ((N + 1)/2, N + 1] for every
  m > N. The derivation splits on a pigeon a: each X(a, j) M comes from the same claim with one
  hole fewer, so one variable is added and one hole removed per step.

## 5. Still open on the list

- L-meta-667: checked as `linear_four_lb` (`MetaComplexity/Helpers/LinearFourLB.lean`) for any m
  4-sets on n <= 15 points that pairwise meet in at most one point: weight-2 AND/OR circuits need
  3m gates. The proof bounds how many lines a gate's set can hold, and that count works only up to
  n = 15 (a set of at most 9 points holds at most 3 lines). For larger n a gate can hold many
  lines, and the count gives only about sqrt(m). Going further needs a lower bound on OR gates for
  large sets, which is new mathematics. For large n, 3m may even be false: big OR sets shared
  by many lines and cut down by AND gates could serve several lines at once, and this proof
  does not rule that out. Open: the least size, as a function of n and m, for linear 4-uniform
  families with no bound on n. `pg23_lb` recovers the 13-line row.
- L-gct-180, 197 and 198: checked as one family, `witness_family` (`Gct/Helpers/WitnessFamily.lean`).
  For every q >= 4 there is a subspace of 4 x q complex matrices of dimension q + 1 with zero row
  sums on which the quadratic, cubic and quartic distinct-column sums vanish. Rows 1 to 3 live on
  columns 0 to 3, so by the row-sum condition each identity sees only those columns.
- Harder:
  - L-meta-573, 574 and 576 for h = 1 and h = 2. These need new base cases.
