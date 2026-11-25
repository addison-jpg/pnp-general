# Transit: the bus network on the hairy ball

Source: the hairy ball idea is in `brain/cortex/BASE.md`. The bus reading is this build's own. No earlier doc shows Addison brought buses. Idea: buses wander a network drawn on the hairy ball. How long until a bus has been to every stop?

Model. A bus at a stop moves to a neighbouring stop chosen uniformly at random (a simple random walk). The cover time is the expected number of moves until every stop is visited.

| # | Claim | Label | Result |
|---|---|---|---|
| 1 | For every connected graph on 2 to 6 vertices (142 up to isomorphism) and every start, the exact cover time is at most 2m(n-1). | checked-finite | `check.py`, exact fractions |
| 2 | The bound 2m(n-1) holds for every connected graph. | paper | Aleliunas, Karp, Lipton, Lovasz, Rackoff 1979 (cite; not read here) |
| 3 | On a sphere, the indices of a field's zeros sum to 2 (Poincare-Hopf). | paper | cite; the discrete version is checked in `brain/cortex/` |

Run: `python3 -I transit/check.py` (about 3 s). The largest ratio cover/bound is 5/8 (the path on 3 stops, started in the middle).

What this is not. It does not say buses on a sphere must stall. Item 3 is about fields, item 1 is about walks. The frame joins them as a reading, not as a theorem.
