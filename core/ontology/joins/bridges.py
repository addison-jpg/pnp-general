"""Join social + philosophy: every bridge (philosophy/rhizome.py, critical edge) is a local bridge
(culture/social/weakties.py, endpoints share no neighbour); not conversely. Every labelled graph, 1..6 vertices."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from load import load
rh = load("philosophy/rhizome.py"); bridges = local = with_lb5 = 0
for n in range(1, 7):
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        E = [p for k, p in enumerate(pairs) if mask >> k & 1]; adj = [0] * n
        for a, b in E: adj[a] |= 1 << b; adj[b] |= 1 << a
        lb = [(a, b) for a, b in E if not adj[a] & adj[b]]        # weakties: no shared neighbour
        if n <= 5: with_lb5 += bool(lb)
        if not rh.connected(n, adj): continue
        for a, b in E:
            adj[a] ^= 1 << b; adj[b] ^= 1 << a; br = not rh.connected(n, adj); adj[a] ^= 1 << b; adj[b] ^= 1 << a
            bridges += br; local += (a, b) in lb
            assert not br or (a, b) in lb, (n, E, (a, b))
assert with_lb5 == 896 and local > bridges                                             # the count weakties.py prints
print(f"connected graphs on 1..6 vertices: {bridges} bridge edges, {local} local-bridge edges; every bridge is a local bridge")
print("graphs on 1..5 vertices with a local bridge: 896, as culture/social/weakties.py counts"); print("PASS")
