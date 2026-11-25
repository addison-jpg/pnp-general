# love

Who to pursue, as a small finite model. Monogamy and polyamory are one model with a capacity k.
Run `python3 -I culture/love/check.py` (about 3 s) or `bin/asteroid --no-lean love.ath`.
Tests: `python3 -I culture/love/test_love.py`.

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

n=4 is not run. It has 24^8 profiles, about 1.1e11. The bound is n <= 3.

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

## Sources (cited, not re-read here)

- Stable marriage and deferred acceptance: Gale and Shapley 1962. Cited from memory.
- The many-to-many (capacity) version is a known generalisation. Cited from memory, not re-derived.
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

- n=4 and above: not run.
- Whether the pursuit rule is good advice for a person: not a question this model can answer.
