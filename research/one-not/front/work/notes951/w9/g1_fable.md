# g1_fable.md — task G1 (global double counting of minimality), restart-safe log
Tools: w9/g1/g1lib.py (bitmask truth tables; sub(c,T,Z,O,keep) = alive gates + base of ANY sub-instance x_Z:=0, x_O:=1, outputs kept;
cleanup = functional dedupe against constants/variables/earlier wires + cone of surviving outputs), stats.py, lp.py, satgen.py.

## G1.0 What plain summation can and cannot do (PROVED, trivial)
N2 and N3 are PER-POINT constraints. Summing them over v only loses information unless the left side has a lower bound that is not
per-point. Sum N2 = "sum_v dead0(v) <= sum|S| - n*sigma"; this contradicts sigma>=1 iff some v has dead0(v) >= deg(v), i.e. iff (K) holds.
Slot identity (exact): 2s-1 = sum_v readers(v) + sum_g fanout(g)  =>  in a counterexample
   sum_v (deg(v)-readers(v)) = 1 + sigma + (#outputs that are read) + (excess fan-out of gates).   (no constraint by itself)
Barrier check (coordinator, Wegener 1-slice remark): reader counts alone are unit-vector information; every useful step below uses an input
of weight >= 2 (the absorbing assignment x_v=1 in P2, full-subcube restrictions in N2). Pure reader/unit counting cannot close the problem.

## G1.1 THEOREM (PROVED): s >= base for EVERY (1,1)-disjoint system in which every point has degree <= 2 (any set sizes; all grids, 4x3 incl.)
Class C2 = systems with max point degree <= 2; closed under point deletion. Take a counterexample in C2 minimising (sum|S|, s).
(a) [N2] x_v:=0 gives a correct one-NOT circuit for {S_w\v} (in C2, smaller sum|S|), all direct readers of x_v are removable
    (x_v|c -> c, x_v&c -> 0, ~x_v -> 1, constants propagate), base loss = deg(v). So readers(v) <= deg(v) - 1.
    A variable of degree 0 has no reader (else x_v:=0 gives a smaller circuit for the same system). Every variable in a set has >= 1 reader.
    Hence every point has degree exactly 2 and EXACTLY ONE reader.
(b) [P2, absorbing lemma] If x_u (deg(u) >= 1) has exactly one reader r, then r is not x_u|x_v (v != u, provided some set through u avoids v:
    true if deg(u)=2 or the set is not {..u,v..}), not x_u&x_v, not ~x_u, not x_u o x_u.
    Proof: r = x_u|x_v: put x_v=1, all other variables 0; no wire changes when x_u is toggled, but OR(S_b) does for S_b∋u, v∉S_b.
    r = x_u&x_v: put x_v=0, others 0. r = ~x_u = N: every wire is a monotone function of (x,N) (only one NOT), so with the other variables 0
    no output can go 0->1 when x_u goes 0->1. r = x_u o x_u computes x_u: then r and every reader of r die under x_u:=0, 2 > deg-1.
(c) The first gate of the circuit reads only input variables: it is x_u o x_v or ~x_u, and it is the unique reader of x_u. Contradiction with (b). ∎
Uses: one NOT (in (b)), weight-2 inputs (in (b)), |S∩S'|<=1 (some set through u avoids v). Does not use h(0)=0, hardness, DD, cleanliness.
CHECKED: satgen.py pasch (all degrees 2) with "every variable has <= 1 reader": UNSAT at s = 9, 10, 11 (consistent: (b)+(c) show such a
circuit exists for NO s). alcheck.py: 55 single-reader variables in badT/bad/c/k/cxtw3c: 0 violations of the absorbing lemma.

## G1.2 PROVED: bottom lemma (any minimal counterexample; sigma = base - s >= 1)
V1 = points with exactly one reader (contains every point of degree <= 1+sigma), B = points with >= 2 readers (degree >= 2+sigma).
Every point has degree >= 2 (1 <= readers <= deg - sigma).
(AL) v in V1, reader r = x_v o c: c is a GATE, x_v-free, and for every set S∋v: r = x_v|c => c <= OR(S\v) pointwise;
     r = x_v&c => c = 1 wherever OR(S\v) = 0.   [o_S must be sensitive to x_v at every z vanishing on S; c is not a variable since
     deg(v) >= 2 and the sets S\v are disjoint; r != ~x_v by the antitone argument.]
(B2) |B| >= 2: first gate is x_u o x_v (both in B by P2) or N = ~x_u (u in B); in the latter case the second gate is x_a o x_b (both in B)
     or N o x_v, and then v in B (N|x_v: put x_u=0, rest 0; N&x_v: put x_u=1, rest 0, a set through v avoids u).
     => sigma <= (second largest degree) - 2;  s >= base for every system with at most ONE point of degree >= 3.

## G1.3 PROVED: PEELING / CASCADE LEMMA
Order V1 by the position of the reader: v_1, v_2, ...; A_j = B ∪ {v_1..v_{j-1}}; c_j = the other input of the reader r_j of v_j.
c_j is syntactically a function of the variables in A_j only. For every j and every set S∋v_j, with T = S ∩ A_j:
 (i)  T != ∅  (else c_j is constant: c_j(x) = c_j(x|A_j) and x|A_j vanishes on S\v_j);
 (ii) if T = {u}: under x_u := 0 the gate c_j becomes constant and r_j becomes x_{v_j}; both die, in addition to the readers of x_u
      (r_j is not a reader of x_u). So dead0(u) >= readers(u)+1 >= 3 if u in B, >= 2 if u in V1; with N2:
      deg(u) >= 3+sigma (u in B) resp. deg(u) >= 2+sigma (u in V1).
 (iii) (two-point version, from minimality under x_T := 0, T = {u1,u2} both with readers = deg - sigma, sigma = 1): c_j is a direct reader
      of x_u1 or x_u2, or a gate x_u1 o x_u2 exists. [dead(T:=0) >= |R_u1 ∪ R_u2| + 1 + [c_j not in R_u1 ∪ R_u2] <= deg(u1)+deg(u2)-sigma.]
 Uses multi-weight inputs through AL and through the restriction x_u := 0 on the whole subcube (not unit-vector information).
COVERAGE TEST (w9/g1/cover.py): covered(system) := all |S| <= 3, or R0-deletable point (recursively), or [all point deletions covered and
 NO scenario (sigma, B with |B| >= 2, B ⊆ {deg >= 2+sigma}) admits a peeling order satisfying (i),(ii)].
 PROVED-BY-CHECKER (s >= base):  the n=8 core system {0123},{045},{146},{256},{347},{157} (each low point lies in a set whose only
 degree-3 point has degree 3 < 3+sigma: sets {0123}, {256}, {347}); all its point deletions are covered by small3/R0;
 the 4x3 and 4x4 grids (G1.1). By hand for core8: sigma = 1, low points 0,2,3,6,7 are V1; L_v|H = x1&(x4|x5), x1&x5, x1&x4, (x1|x4)&x5,
 x4&(x1|x5): each vanishes when one degree-3 variable is 0, so the first V1 reader gives dead0(u) >= 3 > deg(u)-1 = 2.
 FRONTIER (explore.py, 4000 random systems with a 4-set, n <= 11): 858 non-trivial cores covered, 288 NOT covered. Smallest uncovered:
 n=8, e.g. {1,3,4,5},{3,10},{1,9,10},{5,10},{0,4,6,10},{3,6,9},{0,5,9} (scenario sigma=1, B={3,5,9,10});
 {0,1,2},{0,3,7},{1,6,7},{2,7,9},{1,3,9},{0,4,9},{2,3,4,6} (B = the six degree-3 points). Uncovered = systems where every point lies
 only in sets containing >= 2 "possible B" points, in particular ALL systems with every degree >= 3 (scenario B = everything, V1 = ∅:
 the lemma says nothing; e.g. PG(2,3)).

## G1.4 Numerics on real circuits (all far above base; stats.py, lp.py, rconj.py)
Tightness of the summed constraints (surplus = dead - loss; a minimal counterexample needs <= -sigma for EVERY v):
 cx1 (s=22, base 7): sum_v surplus0 = +16, max 5; sum_v surplus1 = +104, max 15 (= slack). cx3: sum0 = +9, max0 = 1, max1 = 15.
 cfgI: sum0 +22, max0 9, max1 18 (= slack).  badT(63): min over circuits of max_v surplus0 = 5 = min slack; bad(160): 3; c.jsonl(2321): 2.
 Reader deficiency sum_v (readers - deg): cx1 +8, cx3 +8, cfgI +11 (data circuits have MORE readers than degree; N2 is far from tight).
 Output deletion (single set): max surplus cx1 5, cx3 2, cfgI 4; min over data 0..1.
INDUCTION LP (fractional (K)):  V = max sum_rho lambda_rho base(rho)  s.t. every gate is alive in total lambda-weight <= 1, rho over proper
 sub-instances (A: x_v:=0, B: x_v:=1, C: delete one output, D: two zeros, E: single set alone, F: x_u:=0,x_v:=1, G: zero a whole set).
 V >= base on a circuit whose sub-instances satisfy the bound gives s >= base. CHECKED: family AB: V >= base on badT(63), bad(160), c(2321),
 cx1, cx2, cx3, cfgI; V < base on cxtw3c (6 < 7), cxr (5 < 6), cxe3 (9.75 < 10). Family ABCD(F): cxr still 5 < 6. Full family A..G:
 V >= base on every circuit tested (cxr 7, cxe3 11.5, cxtw3c 7.0 exactly, cx44_1 6.0 exactly: tight). CONJECTURE FK (unproved, data are
 junk-heavy): V_{A..G} >= base for every clean correct one-NOT circuit. Zeros alone (A) fail often (V = base-1).
REFUTED (paper): (R) s >= base + sum_v (deg(v)-readers(v))^+.  Monotone junk: M a point set meeting every set twice, T = AND(M),
 r_v = x_v|T for all v, honest OR-trees over the r_v: s = base + n + |M| - 1, readers = 1 off M and 2 on M. Plane of order 3, M = three
 non-concurrent lines minus nothing (9 points): s = base+21 < base+30. So reader deficiency is purchasable by monotone junk at additive cost
 n+|M|-1; what kills it in a minimal counterexample is the cascade (x_u:=0, u in M, kills T and all r_v) = G1.3.

## STATUS (G1)
PROVED: G1.1 (max degree <= 2), G1.2 (|B| >= 2, at most one point of degree >= 3), G1.3 (peeling lemma) => core8, grids, 858/1146 random cores.
NOT PROVED: no minimal counterexample in general. Exact gap: scenarios where every set through every single-reader point contains >= 2
 multi-reader points (each of degree >= 3), incl. all systems with min degree >= 3. There the junk gate c_v <= AND_S OR(S∩B) survives every
 single x_u := 0; next tools: (iii) two-point restrictions x_T := 0 (T = S∩B), and x_u := 1 (N3) on the bottom part P (gates over B only).

# ROUND 2 (gap: V1 empty / every set through a single-reader point has >= 2 B-points)
Tools: w9/g1/enumcores.py (level-wise isomorph-free enumeration of skeleton cores = partial linear spaces, all lines >= 3, every point on
>= 2 lines, some line >= 4; reproduces research's counts 4 / 50 / 1538 for n = 8 / 9 / 10; cores{8,9,10}.pkl), cover2.py (checker with the
rules below; DFS over peeling orders with capacities; sound over-approximation of "a minimal-counterexample scenario exists").
Convention: minimal counterexample, sigma = base - s, def_u = deg(u) - readers(u) >= sigma; u TIGHT iff def_u = sigma.
All sub-instances x_Z := 0 satisfy the bound, i.e. dead(Z:=0) <= loss(Z) - sigma (loss(Z) = sum_{u in Z} deg(u) when Z lies in one set S, Z != S).

## G1.5 PROVED: AND-reader / NOT-reader lemma
If g = x_u & c (or N = ~x_u) reads x_u, then under x_u := 0 g is constant and EVERY reader of g dies; g has a reader (g <= x_u is no
output) and by cleanliness no reader of g reads x_u. So dead0(u) >= readers(u) + fanout(g).  Hence a TIGHT point has only OR-readers
x_u | c and is not read by N; in particular the reader of a point of degree 1+sigma is r = x_v | c ("OR-type"), and the bottom gates
on tight points are ORs of two variables.

## G1.6 PROVED: capacity form of the cascade (ii')
If k single-reader points v use u as the ONLY earlier point of one of their sets (S ∩ A_j = {u}), the k gates r_v are distinct non-readers of
x_u that die under x_u := 0:  k <= deg(u) - sigma - readers(u)  (<= deg(u)-sigma-2 for u in B, <= deg(u)-sigma-1 for u in V1).

## G1.7 PROVED: TIGHT-PAIR LEMMA (sigma = 1; v of degree 2, sets S_1, S_2, T_i = S_i ∩ A_j, r = x_v | c, c <= OR(T_1) & OR(T_2))
Step 1. Let T_1 = {a,b}, both tight. Restriction x_a = x_b = 0: loss = deg(a)+deg(b); dead ⊇ R_a ∪ R_b ∪ {c, r} ∪ (readers of gates that became
 constant). c is not a reader of a or b (it would be x_a | c'' >= x_a, but c <= OR(T_2), a ∉ T_2). So
 readers(a)+readers(b) - tau + 2 + extra <= deg(a)+deg(b) - 1, i.e. tau >= 1 + extra, tau = #gates reading both x_a and x_b (<= 1: only the OR).
 If a or b is in V1, tau = 0 by P2: CONTRADICTION. Otherwise g1 = x_a | x_b exists, becomes 0, all its readers die and none is a reader of
 x_a, x_b (clean) nor r; so the ONLY reader of g1 is c, and c = g1 & y (c = g1 | y >= x_a is impossible).   [structure S1]
Step 2. If T_2 = {a',b'} is also a tight pair: c = g1 & g2, g2 = x_a' | x_b' read only by c. Restriction x_a' = x_b' = 0 kills R_a' ∪ R_b'
 (readers(a')+readers(b')-1 gates), c, r AND g1 (unread: its only reader died; g1 is no output):  sum readers + 2 > loss - 1. CONTRADICTION.
Step 3 (rule v). A tight B-point a (degree 3, two readers) cannot be in tight pairs of two different points v, v': both readers of x_a would be
 junk feeders g1 = x_a|x_b (read only by c_v), g1' = x_a|x_b' (read only by c_v'), and c_v(e_a) <= OR(T_2(v))(e_a) = 0 = c_v(0): no wire
 other than g1, g1' distinguishes e_a from 0, but OR(S)(e_a) = 1. CONTRADICTION (weight-1 vs 0 input, using the weight->=2 bound c <= OR(T_2)).
 Uses full-subcube restrictions and unread-gate removal; all steps need weight >= 2 information through AL.

## COVERAGE (cover2.py; "covered" = s >= base PROVED for the system, recursion over point deletions)
 rules                               n=8 (4)   n=9 (50)   n=10 (1538)
 (i),(ii) [round 1]                    3         30          516
 + capacity (ii')                      3         30          523
 + tight pair (iv)                     4         35          603
 + rule (v)                            4         36          657
All four n=8 skeleton cores are now proved (the last one is Fano-like: {012},{034},{056},{135},{146},{367},{2457}).
n=9: 14 open, but only ONE whose point deletions are all covered:
 {012},{034},{056},{078},{135},{146},{367},{2458}  (degrees 4,3,2,3,3,3,3,2,2; scenario sigma=1, B = {0,1,3,4,5,6}).
 Surviving scenario there (derived by hand): point 8 first, using the degree-4 point 0 as singleton: forces readers(0) = 2,
 c_8 = (x4|x5) & x0 read only by r_8 = x8 | c_8, g1 = x4|x5 read only by c_8; then the second reader of x4 is x4 | c' with
 c' <= (x0 & ~x5 & ~x8) | (x3 & (x1|x6) & (x2|x5|x8)), and x_0 = x_3 = 0 forces the second reader of x0 to be x0 o x3. Not closed.
(Skeleton cores only: systems with additional pair-sets are not in these counts; pairs raise degrees and weaken the tight rules.)

## What blocks the remaining cases (exact)
 (a) T = S ∩ A_j of size >= 3, all tight: the restriction x_T := 0 has slack (|T|-1)*sigma, which pays for the two junk deaths (c, r); no rule.
 (b) non-tight points (degree >= 3+sigma, here degree 4) used as singleton or in pairs: structure is forced (see n=9 example) but the case
     tree does not close with one more restriction.
 (c) V1 = ∅ (all points with >= 2 readers, e.g. 3-regular systems, PG(2,3)): partial result only. For a tight a with bottom gate
     g1 = x_a | x_b: the other reader x_a | c' satisfies c'|_{x_b=1} <= OR(S\a) & OR(S'\a) for the >= 2 sets S, S' through a avoiding b
     (c' is a gate; monotone c' is pure junk). So a tight point behaves like a single-reader point relative to the sets not containing b.
     A "relative peeling lemma" for these c' (support on a subcube) is the natural next step; not proved.

# ROUND 3 (relative peeling, N3 route, tight T >= 3, pair-sets, PNP links)
CORRECTION to G1.4 "REFUTED (R)": in the junk construction the points of M need no relay (x_v | AND(M) = x_v), so
 s = base + (n-|M|) + (|M|-1) = base + n - 1 (not base + n + |M| - 1), M any TRANSVERSAL with |M| >= 2; single-reader points: n-|M|;
 points of M have deg+1 readers. (R) stays refuted (deficiency sum = sum_{v∉M}(deg-1) can exceed n-1).

## G1.8 PROVED: relative absorbing lemma (the "half-cube" statement), and where it stops
Tight a in B with exactly two readers g1 = x_a | x_b (earlier) and g2 = x_a | c2. Let S' range over the sets through a avoiding b
(>= deg(a)-1 >= 2 of them). Then c2 is a gate, c2 restricted to {x_b = 1} is x_a-free and  c2|_{x_b=1} <= OR(S'\a)  for every such S'.
 [On {x_b=1} g1 is absorbed, so x_a acts only through g2; same argument as AL in the correct circuit C|_{x_b=1}.]
Monotone case (c2 not downstream of N): c2 <= OR(S'\a) on the WHOLE cube (c2(x) <= c2(x|e_b) and b ∉ S'), so c2 is an ordinary junk gate and
 the cascade applies: if (S'\a) ∩ Supp(c2) = {u} then x_u := 0 kills c2 and g2; dead0(u) >= readers(u)+1; contradiction for tight u.
General case: c2(x) <= OR(S'\a)(x) unless the step x -> x|e_b crosses h (h(x)=0, h(x|e_b)=1). So after x_u := 0 the gate c2 is only known to
 satisfy c2 <= [h(x)=0 & h(x|e_b)=1 & x_b=0]; it need not die. THIS is the exact obstruction: the NOT gate re-enters through crossings at b.
 The same statement holds with "pair-partners" instead of b (G1.9). NOT PROVED: a relative peeling lemma strong enough for 3-regular systems;
 PG(2,3) and all V1 = ∅ systems remain open. It does not become a general induction (see G1.11).

## G1.9 PROVED: pair-set lemma for tight points
Let {v,u} be a pair-set and v tight. All gates whose restriction under x_v := 0 is x_u die (the output o_vu among them); since only readers of
x_v may die, the lowest of them is a reader x_v | c with c|_{x_v=0} = x_u and c not a dying gate, i.e. c = x_u: the gate x_v | x_u EXISTS and is
a reader of both. So a tight point with p pair-sets and l = deg-p lines has exactly l - sigma non-pair readers; they satisfy AL relative to
the subcube where all pair-partners are 1 (monotone case: on the whole cube). Not yet used in cover2.py.

## G1.10 N3 route (x_b := 1) on the bottom part: what it gives
x_b := 1 kills every gate >= x_b (all OR-readers of x_b and everything above them) and makes each a with reader x_a | x_b and two readers a
single-reader point of the restricted (correct, non-minimal) circuit; AL there is exactly G1.8. N3 itself only says
#(gates >= x_b) + #(unread) <= sum_{S∋b} d_S - sigma, and the right side is large (honest circuits meet it with equality only through whole
trees), so on the bottom part N3 yields no new rule: the bottom gates x_a|x_b are >= x_b but there are at most readers(b) of them.
To exploit x_b := 1 one needs a SURCHARGE theorem for non-minimal circuits (G1.11): then dead1(b) <= sum d_S - sigma - (#points made
single-reader by x_b := 1).

## G1.11 CONJECTURES (strengthened statements; evidence only)
 (H+)  s >= base + kappa, kappa = #single-reader points of degree >= 2.      (Psi1) s >= base + #{v : readers(v) < deg(v)}.
 SAT (hplus.py, Pasch, base 8): with variable 0 forced single-reader the minimum is s = 10 = base+2 for monotone circuits (UNSAT at 8, 9;
 optimal circuit: c = x4 & (x1|x2), r = x0 | c, both sets through 0 built on r), and s = 11 with exactly one NOT (UNSAT 8, 9, 10).
 Junk construction above: surcharge = kappa + |M| - 1 >= kappa + 1. "s >= base + 2*kappa" is FALSE (4x3 grid, |M| = 4, kappa = 8: base+11).
 Why this is NOT a general induction: for a minimal counterexample to (H+)/(Psi1), deleting a deficient point v gives
 dead0(v) <= deg(v) - 1 + (|D| - |D'|), which is no constraint when v itself leaves D; when every point is deficient (the situation of a
 minimal counterexample to 951) single deletions carry no information at all. The peeling lemmas do not turn into a general induction.

## Tight T of size t >= 3 (no rule; exact inequality)
v of degree 2 (sigma=1), T = S ∩ A_j all tight, |T| = t: x_T := 0 gives  tau >= 3 - t + extra  (tau = #gates reading two T-variables,
extra = dying gates other than T-readers, c, r). For t = 3 this is tau >= extra, satisfiable with tau = extra = 0: the two junk deaths
are exactly paid by the slack (t-1)*sigma. A rule needs a second, independent death (as g1 "unread" in G1.7 step 2); none found.

## Cores WITH pair-sets (paircores.py; skeleton + any set of non-collinear pairs, up to isomorphism)
 n=8: 262 systems, 37 covered (by #pairs: 1: 8/9, 2: 14/27, 3: 14/44, 4: 1/59, >=5: 0/123).
 n=9 (random sample): 2178 systems, 202 covered (1: 63/151, 2: 86/439, 3: 46/540, >=4: 7/1048).
 Pairs raise degrees, so points stop being "known tight" and the scenario B = everything opens up. G1.9 is the tool to restore tightness
 (count lines instead of sets for tight points) but is not implemented.

## PNP-SUBPROBLEM LINKS (f_G = OR_{uv in E} x_u & x_v, conjecture |E| + tau(G) - 1; snapshot pnp_sub/)
 * Same induction shape. x_v := 0 turns f_G into f_{G-v}; all direct readers of x_v die; the conjectured value drops by
   deg(v) + (tau(G) - tau(G-v)) in {deg(v), deg(v)+1}. So a minimal counterexample in a deletion-closed class (e.g. C4-free) has
   readers(v) <= dead0(v) <= deg(v) - sigma + [v is in every minimum cover]: the exact analogue of N2.
 * Absorbing lemma transfers (dual form). f_G is sensitive to x_v at z (z_v=0) iff z hits N(v) and f_{G-v}(z) = 0. A single reader
   x_v & c needs c(z) = 1 at all such z ("c >= OR(N(v)) off f_{G-v}"), a single reader x_v | c needs c(z) = 0 there. Consequences:
   a single reader x_v & x_u forces N(v) = {u} (leaf), a single reader x_v | x_u is impossible when deg(v) >= 1 (z = e_w, w in N(v)\u, resp.
   z = e_u). So the first gate x_u o x_v has both variables with >= 2 readers unless it is a leaf AND: this is the G1.1 mechanism and would
   give the bound for max-degree-<=2 graphs (paths, cycles of girth >= 5) in the MONOTONE and one-NOT settings.
 * What does NOT transfer: the case "first gate = NOT x_u" is excluded in 951 only because there is ONE NOT (all wires monotone in (x,N)).
   With arbitrarily many counted NOT gates a variable may be read only through its negation, so P2 and the peeling lemma need a new
   argument there. The cascade lemma (junk gate dies under one more zero) is basis-independent once AL is available.
 * From them: their S2/S4 (C4-free => every biclique is a star, f_G = OR_t x_t & OR(N_t)) is the bridge: a one-NOT circuit for the
   (1,1)-disjoint family {N_t} plus |T| ANDs and |T|-1 ORs computes f_G, so their upper bound |E|+tau-1 is "951-base + 2 tau - 1".
   A lower bound for f_G does not follow from 951 (single output), and nothing in the snapshot (SAT sweeps n <= 7, literature: not
   found) gives a new tool for the 951 gap.
