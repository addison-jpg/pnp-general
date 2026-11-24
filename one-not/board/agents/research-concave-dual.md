# research: the concave dual of MergePrice — when do 0/1 prices suffice? (coord assignment, 2026-11-24 ~09:10)

Target (one-not/README.md): MergePrice for a minimal counterexample: for all π ≥ 0,
    Σ_w m_w(π) ≤ π(G),   m_w(π) := min_z π(M_z(w))   (M_z(w): Lemma M merge set, |M_z(w)| = d_w).
Referee (angle 1): the left side is concave in π, so the inequality on 0/1 prices does not imply it for all π.
Status words: PROVED (short proof below), CHECKED (computed; code one-not/tools/research951/charging/), LIT (citation;
VER = bibliographic data verified via OpenAlex, MEM = standard result from memory, not re-read).
Fable slot: not used (the account's Fable window is closed until about 11:30 UTC; this was done in-session).

## 1. Exact reason (PROVED, elementary: the layer-cake decomposition)
Write π = Σ_t 1_{A_t} (integer levels; real π: π = ∫_0^∞ 1_{π ≥ t} dt), A_1 ⊇ A_2 ⊇ … the level sets. Put
F_w(A) := m_w(1_A) = min_z |M_z(w) ∩ A|. Then π(G) = Σ_t |A_t| and
    m_w(π) = min_z Σ_t |M_z(w) ∩ A_t|  ≥  Σ_t F_w(A_t).
So the 0/1 statement  Σ_w F_w(A) ≤ |A| (all A)  only yields  Σ_w Σ_t F_w(A_t) ≤ π(G), which is WEAKER than MergePrice.
The 0/1 check is a complete proof exactly when, for every chain of level sets, a SINGLE z minimizes |M_z(w) ∩ A_t| at every
level t (chain-uniform minimizers); then m_w is the Lovász extension of F_w and both sides split level by level.
For families of equal-size sets this chain-uniform ('Gale-optimal') property is the greedy property, which characterizes
matroid basis families (LIT, MEM: Rado 1957 'Note on independence functions', Proc. LMS; Gale 1968 'Optimal assignments in an
ordered set: an application of matroid theory', J. Combin. Theory 4; Edmonds 1971 'Matroids and the greedy algorithm',
Math. Programming 1; Lovász 1983 'Submodular functions and convexity': the Lovász extension is concave/convex iff F is
supermodular/submodular).

## 2. The gap on the real instances (CHECKED, the 26 shared instances of tools/w951/tests/instances)
- Merge-set families are not matroid basis families (exchange fails on 18/26: agents/research-charging.md §d).
- Layer-cake gap max_π [m_w(π) − Σ_t F_w(A_t)] over 2- and 3-level chains built from merge sets (chaingap.py):
  positive for 30 of 84 families (15 of 26 instances), up to 2 per family and up to 3 for the SUM over w (cxT4, cx3, v1).
  So a 0/1-only proof loses up to 3 units on concrete circuits (MergePrice itself still holds there: front's MergeFrac checks).
- PER WORLD (chaingap_world.py; world 0 = zero points with h(z) = 1, world 1 = h(z) = 0): the gap is positive for only
  9 of 82 world-0 families and 2 of 84 world-1 families, at most 1 each. Most of the concavity comes from the MIN ACROSS
  THE TWO WORLDS, m_w = min(m_w^0, m_w^1), not from inside a world.

## 3. What the literature offers for integral / 0-1 duals
- Matroids (above): integral, greedy, level-set splitting; matroid union / partition gives the packing min-max (Edmonds 1965;
  Nash-Williams 1966; LIT, MEM). Not applicable as is (not bases), but nearly so inside a world (§2).
- Total dual integrality (LIT, MEM): Edmonds & Giles 1977 'A min-max relation for submodular functions on graphs' (Ann. Discrete
  Math. 1); Giles & Pulleyblank 1979 'Total dual integrality and integer polyhedra' (Linear Algebra Appl. 25); Schrijver,
  'Theory of Linear and Integer Programming' (1986), ch. 22. Standard proof device: UNCROSSING an optimal dual to a laminar /
  chain-supported one. For our LP (rows u_w ≤ π(M_z(w)), unit gate capacities) TDI would follow from total unimodularity,
  e.g. if all merge sets were intervals of one gate order (consecutive-ones property; interval matrices are TU) or the matrix
  were balanced (Fulkerson, Hoffman, Oppenheim 1974 'On balanced matrices', Math. Programming Study 1; LIT, MEM; and
  Conforti & Cornuéjols 1995 'Balanced 0,±1-matrices, bicoloring and total dual integrality', Math. Programming,
  doi 10.1007/bf01590956, VER). Not tested yet on our instances (cheap next check: consecutive-ones of {M_z(w)}).
- Ideal clutters / max-flow-min-cut property (Lehman 1979 'On the width-length inequality', Math. Programming 16; LIT, MEM):
  integral covering duals beyond matroids; recognition is hard in general.
- Economics view = the same LP (LIT): outputs are agents, each must buy ONE bundle from its menu {M_z(w)}; gates are goods with
  supply 1; MergePrice says no price vector makes the cheapest bundles cost more than the goods. Integral (Walrasian)
  equilibria exist when the LP relaxation has an integral optimum (Bikhchandani & Mamer 1997, J. Econ. Theory 74; MEM) and
  under gross substitutes (Kelso & Crawford 1982, Econometrica, doi 10.2307/1913392, VER; Gul & Stacchetti 1999, J. Econ.
  Theory 87, MEM), which is M♮-concavity (Fujishige & Yang 2003, Math. Oper. Res. 28, MEM; Murota, 'Discrete Convex Analysis',
  SIAM 2003, doi 10.1137/1.9780898718508, VER; survey Shioura & Tamura 2015, J. Oper. Res. Soc. Japan, doi 10.15807/jorsj.58.61,
  VER). Unit-demand-over-a-family valuations are gross substitutes essentially when the family is a matroid basis family, so
  again: within a world nearly yes, across worlds no.
- Submodular set cover (Wolsey 1982, Combinatorica 2; LIT, MEM): greedy approximation, not exact; not useful for an exact bound.

## 4. Recommendation for the proof (front lanes A/B): a TWO-WORLD CHAIN LEMMA
Split m_w = min(m_w^0, m_w^1). If inside each world the family were chain-uniform (true for 73 of 82 / 82 of 84 families on the
instances by exchange, and 73/82 / 82/84 by layer-cake), then for a FIXED world choice c: W → {0,1} the map
π ↦ Σ_w m_w^{c(w)}(π) is a sum of Lovász extensions and 0/1 checks suffice. MergePrice then follows from:
  (CU) for every chain A_1 ⊇ … ⊇ A_k of gate sets there is ONE choice c with Σ_w F_w^{c(w)}(A_t) ≤ |A_t| for all t,
plus a repair term for the few within-world gaps (≤ 1 per family on the data). (CU) is a statement about chains and 0/1
sets only, so it is the natural 'shift/exchange' replacement for checking 0/1 prices: it is exactly what the layer-cake
argument needs. Suggested scaffold test: check (CU) exhaustively on the 26 instances and on the 15,300-circuit corpus.
