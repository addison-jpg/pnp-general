#!/usr/bin/env python3
"""Tree against rhizome, by exhaustion over every labelled graph on up to 6 vertices.

Deleuze and Guattari (Mille plateaux, 1980, introduction) set the tree (one root, one path to each point) against
the rhizome (any point connects to any other; a break does not end it). The graph facts under that contrast:
  1. A connected graph is a tree exactly when every edge is critical (removing it disconnects the graph).
  2. Adding one edge to a tree makes the edges of the cycle it closes non-critical, and no others.
  3. The opposite extreme, no critical edge at all (a bridgeless connected graph), is counted for each size.
An edge whose removal disconnects the graph is called a bridge. Every graph is checked; nothing is sampled.
Run: python3 -I philosophy/rhizome.py        (last line is JSON for the board runner)
"""
import itertools, json, time

def connected(n, adj):
    seen, todo = 1, [0]
    while todo:
        v = todo.pop(); new = adj[v] & ~seen; seen |= new
        while new:
            b = new & -new; todo.append(b.bit_length() - 1); new ^= b
    return seen == (1 << n) - 1

def tree_distance(n, adj, a, b):
    dist = {a: 0}; todo = [a]
    while todo:
        v = todo.pop()
        for w in range(n):
            if adj[v] >> w & 1 and w not in dist: dist[w] = dist[v] + 1; todo.append(w)
    return dist[b]

def main():
    t0 = time.time(); graphs = 0; conn, trees, bridgeless = [], [], []
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2)); c = t = r = 0
        for mask in range(1 << len(pairs)):
            edges = [p for k, p in enumerate(pairs) if mask >> k & 1]
            adj = [0] * n
            for a, b in edges: adj[a] |= 1 << b; adj[b] |= 1 << a
            graphs += 1
            if not connected(n, adj): continue
            c += 1; bridges = 0
            for a, b in edges:
                adj[a] ^= 1 << b; adj[b] ^= 1 << a
                bridges += not connected(n, adj)
                adj[a] ^= 1 << b; adj[b] ^= 1 << a
            is_tree = len(edges) == n - 1
            assert (bridges == len(edges)) == is_tree, "fact 1 fails"
            if is_tree:
                t += 1
                for a, b in pairs:
                    if adj[a] >> b & 1: continue
                    d = tree_distance(n, adj, a, b)
                    adj[a] |= 1 << b; adj[b] |= 1 << a; left = 0
                    for x, y in edges:
                        adj[x] ^= 1 << y; adj[y] ^= 1 << x
                        left += not connected(n, adj)
                        adj[x] ^= 1 << y; adj[y] ^= 1 << x
                    adj[a] ^= 1 << b; adj[b] ^= 1 << a
                    assert left == (n - 1) - d, "fact 2 fails"
            if bridges == 0: r += 1
        conn.append(c); trees.append(t); bridgeless.append(r)
    assert trees == [1, 1, 3, 16, 125, 1296]                       # Cayley: n^(n-2)
    assert conn == [1, 1, 4, 38, 728, 26704]                       # connected labelled graphs
    print("vertices 1..6")
    print("connected graphs            ", conn)
    print("trees (every edge critical) ", trees)
    print("no critical edge (bridgeless)", bridgeless)
    print("fact 1 (tree iff every edge is critical) and fact 2 (one extra edge leaves exactly (n-1)-d bridges): hold in every case")
    print("PASS")
    print(json.dumps({"states": graphs, "seconds": round(time.time() - t0, 2), "bridgeless": bridgeless}))

if __name__ == "__main__":
    main()
