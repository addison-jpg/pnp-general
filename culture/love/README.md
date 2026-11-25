# love

Who to pursue, as a small finite model. Monogamy and polyamory are one model with a capacity k.
Run `python3 -I culture/love/check.py` (about 3 s) or `bin/asteroid --no-lean love.ath`.
Paths from any matching: `python3 -I culture/love/paths.py` (about 30 s).
Fractional matchings over Q: `python3 -I culture/love/field.py` (about 30 s).
Tests: `python3 -I culture/love/test_love.py`.
Native (Rust) recomputation and its differential against the Python: `python3 -I culture/love/native_diff.py [--new]` (about 10 s; with `--new` about 50 s). See "Native" below.

## What it models

This models stated rankings, not feelings.
It cannot say who is good for anyone.
No real people, no names, no profiles.

Two sides, A and B, each of size n. Every member ranks every member of the other side, strictly.
A matching is a set of A-B pairs. With capacity k, each member holds at most k partners.
k=1 is monogamy (one-to-one). k=2 is polyamory here.
A pair outside the matching blocks it when both would take each other:
each has a free place, or ranks the other above its worst current partner.
A matching is stable when nothing blocks it.

## Facts (checked-finite: exact, every profile, n <= 3)

In this table the bound is n <= 3. n=4 has 24^8 profiles, about 1.1e11; it is done at k=1 only, natively, by symmetry (see "Native").

| n | profiles | matchings k=1 | matchings k=2 | unique stable k=1 | unique stable k=2 | most stable k=1 | most stable k=2 |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 2 | 2 | 1 | 1 | 1 | 1 |
| 2 | 16 | 7 | 16 | 14 | 16 | 2 | 1 |
| 3 | 46656 | 34 | 265 | 34080 | 40128 | 3 | 2 |

On every profile, for k=1 and k=2:

1. A stable matching exists (brute force over all matchings).
2. Deferred acceptance (A proposes) returns one of the stable matchings.
3. The mirror: the capacity model at k=1 gives exactly the stable matchings of a separate one-to-one model.
4. At k=1, deferred acceptance gives each a its best partner over all stable matchings.
5. The pursuit rule: pursue what deferred acceptance keeps.
   The check asserts only this: in that matching, no member has a pair it would join that the other would also join.
   That is stability, read one member at a time. It says nothing about honesty or strategy.

From k=1 to k=2 on the same n=3 profiles: the count of stable matchings goes up on 3324, down on 9816,
and stays the same on 33516. Totals: 60324 stable matchings at k=1, 53184 at k=2.
When k >= n (checked for n=1,2 with k=2), the only stable matching is everyone with everyone.

Refusals. A refusal is a negative edge (kismesis-like). Matched pairs are positive (matesprit).
Balance is checked with `balanced_parity` and `balanced_brute`, imported from `culture/homestuck/quadrants/check.py`.
Over every matching and every set of refusals among the unmatched pairs:

| n | k | signed graphs | balanced |
|---|---|---|---|
| 2 | 1 | 56 | 52 |
| 2 | 2 | 81 | 73 |
| 3 | 1 | 5504 | 3461 |
| 3 | 2 | 16064 | 8984 |

Parity and brute force agree on n <= 2 (4 members). n=3 (6 members) uses parity only.
Three couples who each refuse every member of the other couples are not balanced: they need three camps.

## Paths to stability: start where you are

### Facts (checked-finite: every profile and every starting matching, n <= 3, k = 1 and 2)

The move: pick one pair that blocks the current matching. The two pair up.
If one of them is full (k partners), it first drops its worst partner. At k=1: each leaves its partner, if any.
Roth and Vande Vate (1990, cited from memory) prove that at k=1, from any matching, some sequence of moves reaches a stable matching.
`paths.py` builds the whole move graph of each profile and searches back from the stable set once.

| k | n | matchings | starts that cannot reach stability | longest shortest path | profiles with a cycle of moves |
|---|---|---|---|---|---|
| 1 | 1 | 2 | 0 | 1 | 0 |
| 1 | 2 | 7 | 0 | 2 | 2 of 16 |
| 1 | 3 | 34 | 0 | 4 | 27492 of 46656 |
| 2 | 1 | 2 | 0 | 1 | 0 |
| 2 | 2 | 16 | 0 | 4 | 0 of 16 |
| 2 | 3 | 265 | 0 | 6 | 11136 of 46656 |

At k=1 "no start is stuck" is asserted (the theorem, on this finite set).
At k=2 it was not assumed. It came out true for n <= 3. Beyond that it is open here.
Some path always exists, but moves can also go round. Cycles first appear at n=2. One, at k=1:
a0: b0 > b1, a1: b1 > b0, b0: a1 > a0, b1: a0 > a1.
{a0b0} -> {a1b0} -> {a1b1} -> {a0b1} -> {a0b0}, one blocking pair each time.
From {a0b0} the pair a1b1 also blocks, and taking it ends at a stable matching.
On n <= 2 the fast move table is asserted equal to a move built directly from `check.blocking_pairs`.

### Reading (analogy)

This is a reading, not a fact.
The ask: search from right after the memory cache, not from scratch. Start from the situation you are in.
Here that is literal. Any matching is a start, and at k=1 one blocking pair at a time can reach stability from it.
At most 4 steps for n=3 at k=1, at most 6 at k=2.
But a careless order can walk in a circle. Being free to start anywhere does not mean every walk ends.
Calling the search "Beauvoirean" is a name for the reading. Nothing here checks Beauvoir.

## Monogamy and polyamory over Q: fields and weight matrices

### Facts

A fractional matching gives each pair a weight x_ij in Q, with 0 <= x_ij <= 1 and row and column sums <= k.
The integer models above are the 0/1 points. Vertices are enumerated exactly (Fraction, double description).
On n=2 the method is asserted equal to a brute force over every square tight subsystem.

1. Stable polytope at k=1 (Vande Vate 1989, Rothblum 1992, cited from memory). For each pair (i, j):
   x_ij + (sum of x_ij' over j' that i ranks above j) + (sum of x_i'j over i' that j ranks above i) >= 1.
   On a 0/1 point this says the pair does not block.
   Every vertex is integral, and the vertices are exactly the stable matchings found by brute force in `check.py`.
   n=2: all 16 profiles, 18 vertices in all (checked-finite).
   n=3 in Python: profiles number 0, 97, 194, ... in `check.profiles(3)` order, 481 of 46656, 618 vertices in all (tested, sampled).
   n=3 natively: all 46656 profiles (checked-finite, see "Native"): every vertex integral, vertices = stable matchings, 60324 in all.
2. Capacity k as a rational number. The direct k-version, k x_ij + (better for i) + (better for j) >= k,
   is not exact. Every stable matching satisfies it. But at k=2 unstable matchings satisfy it too:
   14 of 16 profiles at n=2 (checked-finite), 466 of the 481 sampled at n=3 (tested).
   Example, everyone with the same tastes: {a0b0, a0b1, a1b0} passes at a1b1 (0 + 1 + 1 = 2), yet a1 and b1 both have room, so a1b1 blocks.
   So no stable polytope is claimed for k > 1. The plain polytope {0 <= x <= 1, row and column sums <= k} is (checked-finite):

| n | k=1 vertices | k=3/2 vertices (fractional) | k=2 vertices |
|---|---|---|---|
| 2 | 7 | 25 (18) | 16 |
| 3 | 34 | 766 (732) | 265 |

   At k=1 and k=2 every vertex is 0/1, and they are exactly the matchings of the integer models (7, 34 and 16, 265).
   At k=3/2 a vertex is [[1, 1/2], [1/2, 0]]: x00=1, row 0 = 3/2, column 0 = 3/2, x11=0.
3. Birkhoff and von Neumann (cited from memory): every doubly stochastic matrix is a convex combination of permutation matrices.
   Each matrix was decomposed exactly, and the sum was asserted to rebuild it.
   Every 3x3 one with entries in (1/q)Z, q=1..6: 6, 21, 55, 120, 231, 406 matrices (checked-finite; the counts fit MacMahon's formula, from memory).
   Every 4x4 one, q=1..3: 24, 282, 2008 (checked-finite). 200 seeded random 5x5 ones, q=7 (tested).

### Reading (analogy)

This is a reading, not a biology claim.
Over Q, monogamy and polyamory are one polytope with a dial k. At k=1 and k=2 its corners are the integer models.
Between them, at k=3/2, most corners are fractional: half a partner is a corner, not a blend.
A fractional matching has the shape of a normalised weight matrix from a presynaptic set A to a postsynaptic set B.
Birkhoff says a doubly stochastic weight matrix is a mixture of one-to-one wirings.
`biology/brain/network` models unweighted directed graphs only. It says nothing about weights.
So the step from fields to neurons is analogy. Whether real synaptic weights rank, match or stabilise this way is open.

## Native: the same model in Rust, checked against the Python

`culture/love/native/` is a Rust crate (std only, no crates). It recomputes, from the same definitions as the Python:
profile and matching counts, unique and most stable matchings at k=1 and k=2, the paths-to-stability table,
the k=1 stable polytope (double description, exact rationals: an i64 fraction with i128 intermediates; overflow aborts),
the direct k=2 inequality count and the b-matching polytopes. On n=2 the double description is asserted equal to a brute force.
`native_diff.py` builds it (output in `$CARGO_TARGET_DIR`, never in the repository), runs it, and compares every number with the
Python fingerprints and with the stable totals `check.py` prints. A mismatch fails. The Python is the reference.

### Differential (checked-finite: Python and Rust agree on every number)

| sequence | Python = Rust |
|---|---|
| preference profiles, n=1..3 | 1, 16, 46656 |
| matchings k=1 / k=2, n=1..3 | 2, 7, 34 / 2, 16, 265 |
| unique stable k=1 / k=2, n=1..3 | 1, 14, 34080 / 1, 16, 40128 |
| most stable k=1 / k=2, n=1..3 | 1, 2, 3 / 1, 1, 2 |
| stable matchings summed k=1 / k=2, n=1..3 | 1, 18, 60324 / 1, 16, 53184 |
| longest shortest path k=1 / k=2 | 1, 2, 4 / 1, 4, 6 |
| profiles with a cycle k=1 / k=2 | 0, 2, 27492 / 0, 0, 11136 |
| starts that cannot reach stability k=1 / k=2 | 0, 0, 0 / 0, 0, 0 |
| stable polytope vertices, n=2 all, n=3 every 97th | 18, 618 |
| direct k=2 inequality admits unstable points, n=2..3 | 14, 466 |
| b-matching vertices k=1 / 3/2 (fractional) / 2, n=2..3 | 7, 34 / 25 (18), 766 (732) / 16, 265 |

The Birkhoff part of `field.py` is not recomputed natively.

### New numbers (only after the differential passes)

1. The k=1 stable polytope on all 46656 n=3 profiles (checked-finite). Every vertex is integral and the vertices are
   exactly the stable matchings: 60324 vertices in all; 34080 profiles have 1 vertex, 11484 have 2, 1092 have 3. About 5 s, 2 threads.
2. n=4 at k=1 (checked-finite, by symmetry). Relabelling A and relabelling B (576 maps) act on profiles. The code takes one
   representative of the A-side lists per orbit, then one representative of the B-side lists under that one's stabiliser,
   and weights each by its orbit size. It asserts the weights sum to (4!)^8 = 110075314176. The same code on n=1..3
   (1, 5, 1300 orbits) is asserted equal to the direct counts. n=4: 191108196 orbits, about 35 s on 2 threads.

| n=4, k=1 | value |
|---|---|
| profiles | 110075314176 |
| profiles with a unique stable matching | 65867261184 (about 59.8%) |
| most stable matchings on one profile | 10 |
| stable matchings summed over profiles | 163661617152 |
| profiles with 1, 2, ..., 10 stable matchings | 65867261184, 35927285472, 7303612896, 861578352, 111479616, 3478608, 581472, 36432, 0, 144 |

No n=4 profile has exactly 9 stable matchings. One profile with 10 (the A lists are the rows of a Latin square; the B lists are the same rows in reverse order):
a0: 0 1 2 3, a1: 1 0 3 2, a2: 2 3 0 1, a3: 3 2 1 0; b0: 3 2 1 0, b1: 2 3 0 1, b2: 1 0 3 2, b3: 0 1 2 3.
The Python reference recounts that profile and gets 10. That the most for n=4 is 10 agrees with the literature as remembered
(cited from memory, not re-read). n=4 at k=2 and n=5 are not run.

## Sources (cited, not re-read here)

- Stable marriage and deferred acceptance: Gale and Shapley 1962. Cited from memory.
- The many-to-many (capacity) version is a known generalisation. Cited from memory, not re-derived.
- Paths to stability: Roth and Vande Vate 1990. Cited from memory.
- Fractional stable matching polytope: Vande Vate 1989, Rothblum 1992. Cited from memory.
- Birkhoff 1946 and von Neumann 1953 (doubly stochastic matrices). Cited from memory.
- The 3x3 count formula (q+1)(q+2)(q^2+3q+4)/8: MacMahon. Cited from memory; the counts here are enumerated.
- Structural balance: Cartwright and Harary 1956, as cited in the quadrants check.
- The quadrant names and signs are cited from the Homestuck fan wiki (fanlore.org, mspaintadventures.fandom.com), not reproduced.

## Reading (analogy)

This is a reading, not a fact.
A stable matching is a place where no two people would both rather leave for each other.
Monogamy and polyamory are the same rule with a different k.
On the same tastes, more room (k=2) gave fewer stable outcomes more often than more (9816 profiles against 3324, n=3).
Deferred acceptance is a fast search: each member walks down one list once.
That is why it can work downstream, at any level where things rank each other (neurons, cells, universes).
Whether those things really rank each other is open.

## Open

- n=4 at k=2, n=4 paths and polytope, and n >= 5: not run. n=4 at k=1 is done natively (unique and most stable only).
- Paths at k=2 beyond n=3: whether every start can reach stability.
- A linear description of stability for k > 1 (the direct one fails; comb-type inequalities from the literature are not tried here).
- Whether neurons' weights behave like any of this.
- Whether the pursuit rule is good advice for a person: not a question this model can answer.
