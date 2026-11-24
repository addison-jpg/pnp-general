# ce3: why the two-world menu {0, top_S} fails, and what fixes it

Instance: /home/user/c951/tools/w951/tests/instances/scaffold-951__payment__ce3.json (n=8, s=34).
Script (scratch, not kept): w951 systems.system + systems.merges, atoms z|(1<<u), as in the task statement.
Labels: CHECKED = I ran it; GUESS = not run.

## 1. Data (CHECKED)
Sets S0={0,2,4}, S1={1,2,6}, S2={0,3,5}, S3={1,3,7}; outs 25,35,30,41.
h = wire 8 = x0|x1; NOT = wire 9 = ~(x0|x1).

| set | M_0     | M_top   |
|-----|---------|---------|
| S0  | {10,21} | {17,22} |
| S1  | {10,31} | {17,32} |
| S2  | {11,26} | {17,27} |
| S3  | {11,41} | {17,40} |

All eight (set, world) systems are good (NOT=1 at z=0 and NOT=0 at top). CHECKED.

## 2. Why no {0, top} choice is disjoint (CHECKED: all 16 choices fail)
Conflicting pairs:
- (S0,0)-(S1,0) share g10; (S2,0)-(S3,0) share g11.
- (Si,top)-(Sj,top) share g17 for all 6 pairs.
- No mixed (0,top) conflicts.
So the 0-conflict graph is the perfect matching {S0S1},{S2S3}, and the top-conflict graph is K4.
K4 allows at most one set at top. Each matched pair needs at least one set at top. So at least 2 sets
must be at top, which is impossible.

The shared gates (none is downstream of the NOT, c.downstream()):
- g10 = x2 | h = x2|x0|x1. Monotone and not downstream. It reads h directly. At z=0 it merges the
  shared point x2 with the h-light atom (x0 for S0, x1 for S1).
- g11 = x3 | h = x3|x0|x1. Monotone and not downstream. Same as g10, with shared point x3 (S2, S3).
- g17 = (x2&x3) | (x4&x5&x6&x7). Monotone and not downstream. At top_S every set has its two
  "private" coordinates set: at top_S0 = x1,x3,x5,x6,x7 = 1, both x2 and x4 turn g17 on, and the
  other sets behave the same way. So g17 merges in all four top worlds.
  (The usual pattern is a sum of products whose blocks get completed by each set's top.)

## 3. A disjoint all-world choice (CHECKED)
The full search over all 2^5 zero points per set finds 388 disjoint choices (counted by distinct
merge-set tuples). Two on-menu worlds are never enough, but one off-menu set always suffices.
Example: S0 at 0 -> {10,21}; S2 at 0 -> {11,26}; S3 at top -> {17,40};
S1 at z = e0 (x0=1, everything else 0) -> {32,35}.
At z=e0, h=1 and NOT=0 (the h=1 phase), but z is far below top_S1. CHECKED, and good=True there.
g32 = x6|x1|~h and g35 is S1's output; both are downstream of the NOT.
The same works with S0/S2/S3 in that role. CHECKED: for each i there is a choice with only Si off-menu:
- S0 at e1 or e1+e3 -> {22,25} or {22,24};
- S1 at e0 or e0+e3;
- S2 at e1, e1+e2 or e1+e2+e4;
- S3 at e0, e0+e2 or e0+e2+e6.
In each case the point is a low zero point that turns on h (one bit of {x0,x1}), which leaves the
0-world's h-gate (g10/g11) while staying out of g17.

## 4. Same mechanism as ADV3?
Combinatorially it is the same obstruction. CHECKED: a cover of the choice space by a 0-conflict
graph and a top-conflict graph, with no mixed conflicts, where "at most one 0 per conflict edge" plus
"at most one top per conflict edge" is infeasible. ADV3 does it with a triangle on both sides; ce3
uses a matching on the 0 side and K4 on the top side. In both, the (top,top) conflict is a monotone,
non-downstream gate. CHECKED for ce3 (g17). For ADV3 the record (fable_worlds.md) gives
g25/g32/g39; I did not re-check that they are non-downstream (GUESS).

The (0,0) side differs in detail. In ADV3 the shared gate is the h wire itself (g21 = h, CHECKED: h_wire=21),
which sits in M_0 of all three sets. In ce3 the shared gates are g10 = x2|h and g11 = x3|h (CHECKED). These
are monotone gates that read h, so each is shared only by the two sets that meet on x2 or x3, not by
all four sets. The h-tree flavour is the same: the atoms that make h=1 at z=0 are merged with the
shared point. The fix is also the same. Move one set to a small zero point that already has h=1
(ce3: e0 or e1; ADV3: e11 or e7, where h=1 is CHECKED). That kills the h-gate merge without entering
the top-world junk gate.
My verdict (GUESS, interpretive): it is the same mechanism, an h-tree (0,0) conflict plus a monotone
(top,top) conflict. ce3 is a sparser variant in which the h-conflict is "h OR shared-point" restricted to
pairs, and the top conflict is a single 4-way gate. It is a different gadget, not a new kind of obstruction.
Both instances need exactly one off-menu world: CHECKED for ce3 (min = 1); ADV3 has 2 off-menu sets in the cited example (GUESS that 1 suffices there).
