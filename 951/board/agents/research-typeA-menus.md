# research: circuit-free type-A menus and the three open collision types (coord task 11 UTC; official target PureSDR)

Notation: h = the NOT's input (monotone), Min(h) = its minterms; for a set w: S_w, top_w = all-ones off S_w (h(top_w) = 1 is
type A), Min_w = {m ∈ Min(h) : m ∩ S_w = ∅}; for X ⊆ [n], ¬X = the point that is 1 exactly off X (so top_w = ¬S_w).
Status: PROVED (argument given), CHECKED (kill test 951/tools/kill_tests/typeA.py on the 63 correct one-NOT circuits with
n <= 10 in the 951 corpus, built exactly as ext.py builds both menus), OPEN.

## (a) I1 zero points (PROVED + CHECKED 273/273 sets)
Z is an I1 point of w (h(Z) = 0, Z ∩ S_w = ∅, Z maximal with these properties) iff Z = top_w \ T with T a MINIMAL
TRANSVERSAL (minimal hitting set) of Min_w. Proof: for Z ≤ top_w, h(Z) = 0 iff no minterm lies inside Z iff T = top_w \ Z
meets every m ∈ Min_w (minterms meeting S_w never lie inside Z); maximality of Z = minimality of T. So the I1 points are the
maximal false points of h on the face {x_{S_w} = 0}; they are the complements (in top_w) of the blocker b(Min_w)
(Edmonds-Fulkerson). Type B (h(top_w) = 0): Min_w = ∅, T = ∅, Z = top_w only.
## (b) I0 atoms (definition, already circuit-free)
Atom of u ∈ S_w: m_u ∪ {u} with m_u ∈ Min(h), m_u ∩ S_w ⊆ {u}; one choice per atom (zero point top_w, tables of C_0).
A choice for u AVOIDING another set S_v exists iff h(¬((S_w ∪ S_v) \ {u})) = 1 (some minterm avoids (S_w \ {u}) ∪ S_v).

## (c) The three open collision types in terms of h and the sets (two sets w ≠ v, |S_w ∩ S_v| <= 1)
(i) I1(w, Z) vs I1(v, Z'), Z' = top_v \ T': |S_w \ Z'| = |S_w ∩ S_v| + |S_w ∩ T'| (T' ⊆ ¬S_v). So the open case
    '|S_w \ Z'| >= 2' is exactly: the minimal transversal T' of Min_v meets S_w in >= 2 - |S_w ∩ S_v| points.
    CHECKED: 0 collisions in 995 pairs with max(|S_w \ Z'|, |S_v \ Z|) <= 1 (consistent with the Lean lemma); 49 collisions
    in 968 pairs with >= 2. Example: Pasch system (data/witnesses/pasch_s14_heavy_atmostone.json) {0,1,2} vs {2,4,5}.
(ii) I0(w, (m_u)) vs I0(v, (m'_u')): open case 'some m_u meets S_v or some m'_u' meets S_w'.
    CHECKED: 0 collisions in 27,670 pairs where all chosen minterms avoid the other set; 180 collisions in 1,067,602 pairs
    where one meets it (e.g. cx44_0, cxT2). By (b) the meeting is FORCED for atom u only if h(¬((S_w ∪ S_v) \ {u})) = 0;
    otherwise the menu can choose an avoiding minterm and the collision disappears.
(iii) I1(w, Z) vs I0(v, (m'_u')): NEW CHECKED PATTERN: collisions occur ONLY when some m'_u' meets S_w, also for Z ≠ top_w:
    0 collisions in 3,331 pairs with Z ≠ top_w and all m'_u' avoiding S_w; 4 in 15,276 pairs with Z ≠ top_w and some
    m'_u' meeting S_w; 1 in 910 with Z = top_w and some meeting. LEMMA CANDIDATE (extends CanonOneNot's D from Z = top_w to
    every I1 point): K_1(w; Z) ∩ K_0(v; m) = ∅ whenever every m'_u' ∩ S_w = ∅. If true, (iii) reduces to the same forced
    condition as (ii): h(¬((S_w ∪ S_v) \ {u'})) = 0 for some u' ∈ S_v.

## Which collisions does |S_a ∩ S_b| <= 1 exclude by itself? NONE
All three types occur in the corpus on systems with pairwise intersections <= 1 (49 / 180 / 5 collisions), so the
intersection condition alone excludes none of them. What it does: in (i) it caps |S_w ∩ S_v| at 1, so a collision needs the
minimal transversal T' to use a point of S_w (>= 1 if the sets meet, >= 2 if disjoint); in (ii)/(iii) it is not involved:
the conditions are the h-values h(¬((S_w ∪ S_v) \ {u})) = 0, i.e. 'every minterm of h avoiding S_w \ {u} meets S_v'.
So after (a)-(c) the open statement is purely about h: when h kills ¬((S_w ∪ S_v) \ {u}) (forced meeting) or a minimal
transversal of Min_v uses >= 2 - |S_w ∩ S_v| points of S_w, show that an alternative pure class exists (PureSDR).
