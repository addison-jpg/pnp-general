# bus: a two-way bus over the route graph

The graph comes from `workshop/route/route.py`. It has three layers: P (program `.ath` files), E (evidence files), M (centre shards).

Two trees share one edge set and run opposite ways.
OUT goes down: P -> E -> M. IN goes up: M -> E -> P.

## Laws (checked in workshop/bus/laws.ath, Python asteroid)

- L1 layer order: OUT edges are P->E or E->M. IN edges are M->E or E->P. No edge skips a layer.
- L2 tree: each tree has no cycle, and each node has at most one parent.
- L3 duality: IN is exactly OUT reversed.
- L4 prune: a child keeps its first parent by sorted order. Later parents are pruned. Pruning is deterministic.

A spiral pass is OUT, then IN, then OUT. A prune in one tree is a prune in both. The bus runs passes until one prunes nothing, and reports that count. A fresh rerun must give the same edges.

## Feed

`feed.json` holds the vector row for each kept node whose name has one, from `workshop/route/memory_vectors.json` and the 7B file if present. Rows only. No model is called.

## Not claimed

The graph carries no claimed meaning. It records which files name which files. The vectors are static token embeddings, not meanings.

Status: L1 to L4 are checked in `workshop/bus/laws.ath` under Python asteroid (17 true, 0 false). The native `ast` binary does not run them yet. Feed (reading vectors from JSON) is not built.
