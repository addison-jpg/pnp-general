"""Social readings of the bus network, checked exactly.

(a) Fisher as an absorbing chain. Every directed graph on 1 to 4 states, self-loops allowed, with every
state having at least one out-edge (2^(n*n) graphs, minus those with a sink). The bus leaves a state along an
out-edge chosen uniformly. We find the closed communicating classes and check, exactly:
  - from a state in a closed class, no state outside it is reachable, and the one-step chance of leaving is 0;
  - from every state, the chance of ending in some closed class is exactly 1;
  - adding one edge u -> v, u in a closed class C, v outside C with v reaching C, leaves C not a closed class.
(b) Granovetter weak ties as bridges. Two cliques K_k (k = 2..5) joined by 0, 1 or 2 edges. Exact cover time
from every start (transit/check.py's method) and exact expected time to hit the other clique.
Standard library, exact fractions. Prints PASS and a last JSON line.

  python3 -I transit/social.py"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check import solve, cover_times

def reach(n, out, s):
    seen = {s}; st = [s]
    while st:
        v = st.pop()
        for u in out[v]:
            if u not in seen: seen.add(u); st.append(u)
    return seen

def closed_classes(n, out):
    R = [reach(n, out, v) for v in range(n)]
    cls = {frozenset(u for u in R[v] if v in R[u]) for v in range(n)}
    return [c for c in cls if all(R[v] <= c for v in c)], R

def absorb_prob(n, out, closed):
    """Chance of ever entering the union of closed classes, from each transient state."""
    inC = set().union(*closed); T = [v for v in range(n) if v not in inC]
    if not T: return []
    idx = {v: i for i, v in enumerate(T)}
    M = [[Fr(0)] * len(T) for _ in T]; b = [Fr(0)] * len(T)
    for v in T:
        i = idx[v]; M[i][i] += 1; p = Fr(1, len(out[v]))
        for u in out[v]:
            if u in inC: b[i] += p
            else: M[i][idx[u]] -= p
    return solve(M, b)

def part_a():
    fails = []; graphs = 0; with_closed = 0; per_n = {}; adds = 0; merged_closed = 0; transient_graphs = 0
    for n in range(1, 5):
        pairs = [(a, b) for a in range(n) for b in range(n)]
        cnt = 0
        for mask in range(1 << len(pairs)):
            out = [[] for _ in range(n)]
            for i, (a, b) in enumerate(pairs):
                if mask >> i & 1: out[a].append(b)
            if any(not o for o in out): continue
            graphs += 1; cnt += 1
            closed, R = closed_classes(n, out)
            if closed: with_closed += 1
            else: fails.append(("no closed class", n, mask))
            for C in closed:
                for v in C:
                    if not R[v] <= C: fails.append(("escape", n, mask))
                    if sum(Fr(1, len(out[v])) for u in out[v] if u not in C) != 0: fails.append(("leak", n, mask))
            ap = absorb_prob(n, out, closed)
            if ap: transient_graphs += 1
            if any(x != 1 for x in ap): fails.append(("not absorbed", n, mask, ap))
            for C in closed:
                for u in C:
                    for v in range(n):
                        if v in C or not (R[v] & C): continue
                        out2 = [o[:] for o in out]; out2[u].append(v); adds += 1
                        c2, _ = closed_classes(n, out2)
                        if C in c2: fails.append(("still closed", n, mask, u, v))
                        if any(C < D for D in c2): merged_closed += 1
        per_n[n] = cnt
    return dict(graphs=graphs, per_n=per_n, with_closed=with_closed, with_transient=transient_graphs,
                edge_adds=adds, enlarged_still_closed=merged_closed), fails

def cliques(k, bridges):
    n = 2 * k
    e = [(a, b) for a in range(k) for b in range(a + 1, k)] + [(a + k, b + k) for a in range(k) for b in range(a + 1, k)]
    e += [(i, k + i) for i in range(bridges)]
    return n, e

def hit_other(n, k, edges):
    """Expected moves from each vertex of clique A until the walk first stands in clique B."""
    adj = [[] for _ in range(n)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    A = list(range(k))
    M = [[Fr(0)] * k for _ in A]; b = [Fr(1)] * k
    for v in A:
        M[v][v] += 1
        for u in adj[v]:
            if u < k: M[v][u] -= Fr(1, len(adj[v]))
    return solve(M, b)

def part_b():
    rows = []; fails = []
    for k in range(2, 6):
        for br in (0, 1, 2):
            if br > k: continue
            n, e = cliques(k, br)
            if br == 0:
                rows.append(dict(k=k, bridges=0, cover="infinite", hit="infinite")); continue
            ct = cover_times(n, e); h = hit_other(n, k, e)
            rows.append(dict(k=k, bridges=br, cover_max=str(max(ct)), cover_from_bridge=str(ct[0]),
                             cover_from_inner=str(ct[k - 1]), hit_from_bridge=str(h[0]), hit_from_inner=str(h[k - 1])))
            m = len(e)
            if max(ct) > 2 * m * (n - 1): fails.append(("bound", k, br))
            # Closed form for one bridge, from the bridge end: 1 + (k-1)/k * (time from an inner vertex),
            # inner vertex: k-1 moves to reach a given vertex, then the bridge end; so h_inner = (k-1) + h_bridge.
            if br == 1:
                hb = Fr(k * (k - 1)) + 1   # solves hb = 1 + (k-1)/k * (k - 1 + hb)
                if h[0] != hb or h[k - 1] != hb + k - 1: fails.append(("hit one bridge", k, h))
    # A second bridge never slows the crossing here.
    by = {(r["k"], r["bridges"]): r for r in rows}
    for k in range(2, 6):
        if Fr(by[(k, 2)]["hit_from_inner"]) >= Fr(by[(k, 1)]["hit_from_inner"]): fails.append(("second bridge", k))
    return rows, fails

def main():
    t = time.time()
    a, fa = part_a(); rows, fb = part_b()
    print(f"(a) {a['graphs']} directed graphs on 1..4 states with no sink {a['per_n']}: every one has a closed class;")
    print(f"    no escape from a closed class; absorption probability exactly 1 in the {a['with_transient']} with transient states;")
    print(f"    {a['edge_adds']} single edges out of a closed class to a state reaching back: none leaves the class closed"
          f" ({a['enlarged_still_closed']} times it merges into a larger closed class).")
    print("(b) two cliques K_k, bridges b: max cover time, hitting time to the other clique from the bridge end and an inner vertex")
    for r in rows:
        if r["bridges"] == 0: print(f"    k={r['k']} b=0: disconnected, cover and hitting time infinite")
        else: print(f"    k={r['k']} b={r['bridges']}: cover max {r['cover_max']}, hit {r['hit_from_bridge']} / {r['hit_from_inner']}")
    for f in fa + fb: print("FAIL", f)
    if fa or fb: sys.exit(1)
    print("PASS")
    print(json.dumps({"graphs": a["graphs"], "edge_adds": a["edge_adds"], "cliques": rows, "seconds": round(time.time() - t, 2)}))

if __name__ == "__main__": main()
