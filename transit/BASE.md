# Transit: the bus network on the hairy ball

Source: the hairy ball idea is in `brain/cortex/BASE.md`. The bus idea is Addison's (ontology/SOURCES.md). Idea: buses wander a network drawn on the hairy ball. How long until a bus has been to every stop?

Model. A bus at a stop moves to a neighbouring stop chosen uniformly at random (a simple random walk). The cover time is the expected number of moves until every stop is visited.

| # | Claim | Label | Result |
|---|---|---|---|
| 1 | For every connected graph on 2 to 6 vertices (142 up to isomorphism) and every start, the exact cover time is at most 2m(n-1). | checked-finite | `check.py`, exact fractions |
| 2 | The bound 2m(n-1) holds for every connected graph. | paper | Aleliunas, Karp, Lipton, Lovasz, Rackoff 1979 (cite; not read here) |
| 3 | On a sphere, the indices of a field's zeros sum to 2 (Poincare-Hopf). | paper | cite; the discrete version is checked in `brain/cortex/` |

Run: `python3 -I transit/check.py` (about 3 s). The largest ratio cover/bound is 5/8 (the path on 3 stops, started in the middle).

What this is not. It does not say buses on a sphere must stall. Item 3 is about fields, item 1 is about walks. The frame joins them as a reading, not as a theorem.

## Social readings

Source: Addison, social applications of the buses (ontology/SOURCES.md). Run: `python3 -I transit/social.py` (about 2 s).

| # | Claim | Label | Result |
|---|---|---|---|
| 4 | Every directed graph on 1 to 4 states with no sink (50978), uniform steps: there is a closed class; from it nothing outside is reachable; absorption probability is exactly 1. | checked-finite | `social.py` |
| 5 | Adding one edge from a closed class C to a state that reaches C leaves C not a closed class (77260 cases; 74008 merge into a larger closed class). | checked-finite | `social.py` |
| 6 | Two cliques K_k, k=2..5. No bridge: cover time infinite. One bridge: finite; hitting the other clique takes k(k-1)+1 from the bridge end. Two bridges: less (k=5: 21 to 11). | checked-finite | `social.py`, exact fractions |
| 7 | Capitalist realism: it is easier to imagine the end of the world than an alternative. | fact (cite) | Fisher 2009, *Capitalist Realism: Is There No Alternative?*, Zero Books. Read status: catalogue entries found by web search; book not read here. |
| 8 | Weak ties bridge dense groups and carry new information. | fact (cite) | Granovetter 1973, "The Strength of Weak Ties", *American Journal of Sociology* 78(6):1360-1380. Read status: citation confirmed by web search; paper not read here. |

Reading (Fisher). A closed class is a reading of capitalist realism: once the bus is in, no way out is reachable. `lean/PEqualNP/Philosophy/Fisher.lean` reads lost futures as unreachable states. An analogy, not a theorem about society.

Reading (Granovetter). A weak tie is a bridge. Without one, the network is not accessible: cover time is infinite. One bridge makes it finite. A second shortens it. An analogy; tie strength is not modelled.
