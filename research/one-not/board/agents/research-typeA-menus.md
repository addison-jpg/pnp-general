> **OFF THE ROUTE (main, 2026-11-24 14:45): written for the target PureSDR, which is false for general correct circuits (cxMU_dd); TypeA.lean stays. Kept for the record; do not build on it.**

# research: circuit-free type-A menus and the three open collision types (coord task 11 UTC; official target PureSDR)

Notation: h = the NOT's input (monotone), Min(h) = its minterms; for a set w: S_w, top_w = all-ones off S_w (h(top_w) = 1 is
type A), Min_w = {m ∈ Min(h) : m ∩ S_w = ∅}; for X ⊆ [n], ¬X = the point that is 1 exactly off X (so top_w = ¬S_w).
Status: PROVED (argument given), CHECKED (kill test research/one-not/tools/kill_tests/typeA.py on the 63 correct one-NOT circuits with
n <= 10 in the 951 corpus, built exactly as ext.py builds both menus), OPEN.

## (a) I1 zero points (PROVED + CHECKED 273/273 sets)
Z is an I1 point of w (h(Z) = 0, Z ∩ S_w = ∅, Z maximal with these properties) iff Z = top_w \ T with T a MINIMAL
TRANSVERSAL (minimal hitting set) of Min_w. Proof: for Z ≤ top_w, h(Z) = 0 iff no minterm lies inside Z iff T = top_w \ Z
meets every m ∈ Min_w (minterms meeting S_w never lie inside Z); maximality of Z = minimality of T. So the I1 points are the
maximal false points of h on the face {x_{S_w} = 0}; they are the complements (in top_w) of the blocker b(Min_w)
(Edmonds-Fulkerson). Type B (h(top_w) = 0): Min_w = ∅, T = ∅, Z = top_w only.
## (b) I0 atoms (definition, already circuit-free)
Atom of u ∈ S_w: m_u ∪ {u} with m_u ∈ Min(h), m_u ∩ S_w ⊆ {u}; one choice per atom (zero point top_w, tables of C_0).
A choice for u AVOIDING S_v \ {u} exists iff h(¬((S_w ∪ S_v) \ {u})) = 1 (some minterm avoids (S_w ∪ S_v) \ {u}).
[Corrected 12:05 per coord / board integrator: the old wording 'avoiding S_v' was wrong when u ∈ S_w ∩ S_v (322 of 866
cases); the h-formula itself was right, 2,619 / 2,619.]

## (c) The three open collision types in terms of h and the sets (two sets w ≠ v, |S_w ∩ S_v| <= 1)
(i) I1(w, Z) vs I1(v, Z'), Z' = top_v \ T': |S_w \ Z'| = |S_w ∩ S_v| + |S_w ∩ T'| (T' ⊆ ¬S_v). So the open case
    '|S_w \ Z'| >= 2' is exactly: the minimal transversal T' of Min_v meets S_w in >= 2 - |S_w ∩ S_v| points.
    CHECKED: 0 collisions in 995 pairs with max(|S_w \ Z'|, |S_v \ Z|) <= 1 (consistent with the Lean lemma); 49 collisions
    in 968 pairs with >= 2. Example: Pasch system (research/data/witnesses/pasch_s14_heavy_atmostone.json) {0,1,2} vs {2,4,5}.
(ii) I0(w, (m_u)) vs I0(v, (m'_u')): open case 'some m_u meets S_v or some m'_u' meets S_w'.
    CHECKED: 0 collisions in 27,670 pairs where all chosen minterms avoid the other set; 180 collisions in 1,067,602 pairs
    where one meets it (e.g. cx44_0, cxT2). By (b) the meeting is FORCED for atom u only if h(¬((S_w ∪ S_v) \ {u})) = 0;
    otherwise the menu can choose an avoiding minterm and the collision disappears.
(iii) I1(w, Z) vs I0(v, (m'_u')): open case = Z ≠ top_w (at Z = top_w CanonOneNot's D gives disjointness when every m'_u'
    avoids S_w). On the 63 small circuits collisions appeared only when some m'_u' met S_w (0 in 3,331 pairs), BUT this was a
    SMALL-SAMPLE ARTIFACT: the lemma candidate 'D1' (D at every I1 point) is REFUTED (research-desktop full kill test,
    agents/research-desktop-lemmaD1-killtest.md: 4 collisions in 179,614 tuples on 31,587 circuits; re-checked independently
    by research with canon.py's merges): n = 4, sets {01},{02},{03},{12},{13}, h = x1 ∨ x3, w = {0,1}, Z = {2} (h(Z) = 0,
    maximal off S_w), v = {0,2}, m = ({3},{3}) (both avoid S_w); K_1(w; Z) = K_0(v; m) = {wire 10 = x0 ∨ w7}. Circuit (gate k =
    wire 4 + k): or(1,3), not(4), or(2,5), and(4,6), or(1,7), or(2,8), or(0,7), and(5,9), or(10,11), or(0,3), or(0,1);
    outs 14,12,13,9,4. So (iii) does NOT reduce to the forced-meeting condition; a corrected condition on Z is open
    (research-desktop is locating where D's argument breaks for Z ≠ top_w).

## Which collisions does |S_a ∩ S_b| <= 1 exclude by itself? NONE
All three types occur in the corpus on systems with pairwise intersections <= 1 (49 / 180 / 5 collisions on the 63 small circuits; (iii) also with all minterms avoiding S_w, see D1 refutation), so the
intersection condition alone excludes none of them. What it does: in (i) it caps |S_w ∩ S_v| at 1, so a collision needs the
minimal transversal T' to use a point of S_w (>= 1 if the sets meet, >= 2 if disjoint); in (ii)/(iii) it is not involved:
for (ii) the condition is the h-value h(¬((S_w ∪ S_v) \ {u})) = 0, i.e. 'every minterm of h avoiding S_w \ {u} meets S_v \ {u}'; for (iii) no h-only condition is known (D1 refuted).
So after (a)-(c) the open statement is purely about h: when h kills ¬((S_w ∪ S_v) \ {u}) (forced meeting) or a minimal
transversal of Min_v uses >= 2 - |S_w ∩ S_v| points of S_w, show that an alternative pure class exists (PureSDR).
