# Routing: planned routes on the map of the outer buses

Source: Addison, map-service routing on OpenStreetMap architecture for the outer buses (core/ontology/SOURCES.md). The buses are in `math/transit/`. Idea: a haphazard bus wanders. A route planner finds the shortest road. How do the two compare, and what do real routers do?

Google's own production method is not public. Nothing here claims to know it. Only published algorithms and published router documentation are cited.

## What routers use (research)

| # | Claim | Label | Source and read status |
|---|---|---|---|
| 1 | Dijkstra's method finds a shortest path between two nodes of a graph with positive lengths. | fact (cite) | Dijkstra 1959, "A note on two problems in connexion with graphs", *Numerische Mathematik* 1:269-271. Read status: citation confirmed by web search; paper not read here. |
| 2 | A* adds a heuristic to the search; with an admissible heuristic it stays optimal. | fact (cite) | Hart, Nilsson, Raphael 1968, "A Formal Basis for the Heuristic Determination of Minimum Cost Paths", *IEEE Trans. SSC* 4(2):100-107. Read status: citation and abstract seen by web search; paper not read here. |
| 3 | Contraction hierarchies: rank nodes, remove them one by one, add shortcuts that keep distances; the query searches only upward. | fact (cite) | Geisberger, Sanders, Schultes, Delling 2008, WEA 2008, LNCS 5038:319-333. Read status: citation and summary by web search; paper not read here. |
| 4 | A survey of route planning on road and transit networks, including CH, ALT and partition methods. | fact (cite) | Bast, Delling, Goldberg, Muller-Hannemann, Pajor, Sanders, Wagner, Werneck 2016, "Route Planning in Transportation Networks", *Algorithm Engineering*, LNCS 9220:19-80 (arXiv 1504.05140). Read status: citation confirmed by web search; not read here. |
| 5 | OSRM (an OpenStreetMap router) has two pipelines: Contraction Hierarchies and Multi-Level Dijkstra (MLD, partition then customize). MLD is the default and allows live traffic updates. | fact (cite) | OSRM README and wiki "Running OSRM" (github.com/Project-OSRM/osrm-backend). Read status: summary by web search; pages not read in full. |
| 6 | GraphHopper offers Dijkstra, A*, bidirectional variants, CH ("speed mode") and a landmark A* ("ALT"). | fact (cite) | GraphHopper blog, "Flexible routing 15 times faster" (2017). Read status: summary by web search. |
| 7 | Valhalla uses bidirectional A* on a tiled, hierarchical graph. | fact (cite) | Valhalla docs, "route overview" and "baldr" (valhalla.github.io). Read status: summary by web search. |
| 8 | Google's production routing method is not public. Its Routes API docs describe outputs, not the algorithm. | fact (cite) | developers.google.com/maps/documentation/routes. Read status: summary by web search. |

## Exact checks

Run: `python3 -I math/routing/check.py` (about 60 s). Every connected graph on 2 to 5 vertices (1+2+6+21 classes up to isomorphism), every weight assignment from {1,2,3}: 106932 weighted graphs, 2661969 ordered pairs.

| # | Claim | Label | Result |
|---|---|---|---|
| 9 | Dijkstra, A* with the halved exact distance, and A* with the one-landmark ALT bound all give the Floyd-Warshall distance, every pair. | checked-finite | `check.py` |
| 10 | A* with the halved heuristic never settles more nodes than Dijkstra (ties: target popped first). | checked-finite | `check.py` |
| 11 | A* with ALT never settles more than the ball d(s,v) <= d(s,t). It can settle more than Dijkstra: 12431 queries, because ALT may give h = 0 to a node other than the target. | checked-finite | `check.py`; first case printed |
| 12 | Contraction with exact witness search, in order 0..n-1 (and in every order for n <= 4): the upward bidirectional query is exact for every pair. | checked-finite | `check.py` |
| 13 | Max shortcuts in order 0..n-1 is C(n-1,2) for n=2..5. Worst case: a star contracted centre first. A good order needs 0 shortcuts on that star. | checked-finite | `check.py`, `routing.ath` |

Item 11 corrects the task's wording. "A* never settles more than Dijkstra" is false with ties for ALT. It holds for the halved heuristic here.

## Down and out

| # | Claim | Label | Result |
|---|---|---|---|
| 14 | Join with transit. Over connected n-stop graphs, the largest hitting time divided by hop distance is n^2-3n+3, for n=2..5. It is the clique K_(n-1) with one pendant stop. This is the bridge-end time k(k-1)+1 of `math/transit/social.py`, with k = n-1. | checked-finite | `check.py`, `routing.ath` |
| 15 | The bus picture made precise: a planned route costs d(s,t). A haphazard bus costs H(s,t) on average, up to (n^2-3n+3) d(s,t) on these graphs, and its cover time is at most 2m(n-1) (`math/transit/` item 2). | join | items 14 and transit |
| 16 | Join with the centre. Snapshot of 2026-11-25: 420 records in `center/shards`, 19 programs. The shards grow, so rerun `check.py` for the current count. Programs are adjacent when records share an evidence file. There are 16 components: {asteroid, circuits}, {brain, other, philosophy}, and 14 programs alone. Every eccentricity is infinite. | checked-finite | `check.py`, read of the current shards |
| 17 | On a sphere, a direction field on the roads must have zeros; their indices sum to 2 (Poincare-Hopf). | fact (cite) | Poincare-Hopf, carried from `math/transit/BASE.md` item 3; not re-searched here. Discrete version checked in `biology/brain/cortex/`. |

Reading (item 16). The hard-to-reach edge of the balloon is most of it. Programs cite their own files. Shared evidence is rare. A record linked by program only stays in its program. This measures how the centre is written, not how the ideas relate.

Reading (item 17). A road map on the sphere cannot give every crossing a direction that varies smoothly. That is an analogy for the outer buses, not a check.

What this is not. It does not say how Google Maps routes. It does not test continent-sized graphs, time-dependent weights, or MLD. The infinite family (all graphs) is open; the algorithms are proved correct in the cited papers.
