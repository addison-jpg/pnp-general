"""Regenerate 951 core test systems (research-cores.md). Needs nauty (apt: nauty) and networkx.
Usage: for m in $(seq 3 16); do nauty-genbg -q -Z1 -d2:3 N $m; done | python3 cores.py N        (skeletons, sets >= 3)
       for m in $(seq 3 16); do nauty-genbg -q -Z1 -d2:2 N $m 0:$((MAXBASE+m)); done | python3 cores.py N   (with size-2 sets)
Prints 'base [sets]' for systems with pairwise intersections <= 1 (genbg -Z1), a set of size >= 4, and every point in >= 2
sets of size >= 3."""
import sys, networkx as nx
n = int(sys.argv[1])
for line in sys.stdin:
    g = nx.from_graph6_bytes(line.strip().encode())
    L = [sorted(g[v]) for v in range(n, g.number_of_nodes())]
    if max(len(x) for x in L) < 4: continue
    if any(sum(1 for x in L if p in x and len(x) >= 3) < 2 for p in range(n)): continue
    print(sum(len(x) - 1 for x in L), L)
