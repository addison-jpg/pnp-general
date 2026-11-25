"""Bus network on a small map: exact cover time of a simple random walk.

A bus picks a neighbouring stop uniformly at random. The cover time from stop s is the expected number of
moves until every stop has been visited. This script computes it exactly, in fractions, for every connected
graph on 1 to 6 vertices (one per isomorphism class) and every start, and checks the bound
    cover time <= 2 m (n - 1)
of Aleliunas, Karp, Lipton, Lovasz and Rackoff (1979), where m is the number of edges.
Sanity checks: the path from an end gives (n-1)^2; the complete graph gives (n-1) H(n-1).
Exact rational arithmetic, standard library only. Prints PASS on success.

  python3 -I transit/check.py"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr

MAXN = 6

def canon(n, edges):
    best = None
    for p in itertools.permutations(range(n)):
        e = tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in edges))
        if best is None or e < best: best = e
    return best

def classes():
    """Connected graphs up to isomorphism. Every connected graph on n vertices has a vertex whose removal
    leaves it connected, so adding one vertex to each class on n - 1 vertices reaches every class on n."""
    out = {1: {()}}
    for n in range(2, MAXN + 1):
        got = set()
        for g in out[n - 1]:
            for k in range(1, 2 ** (n - 1)):
                e = list(g) + [(i, n - 1) for i in range(n - 1) if k >> i & 1]
                got.add(canon(n, e))
        out[n] = got
    return out

def solve(M, b):
    """Gaussian elimination over the rationals."""
    k = len(b); M = [row[:] + [b[i]] for i, row in enumerate(M)]
    for c in range(k):
        p = next(r for r in range(c, k) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(k):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][k] / M[i][i] for i in range(k)]

def cover_times(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    full = (1 << n) - 1
    C = {}   # (visited set S, position v) -> expected moves to cover
    for S in sorted(range(1, full + 1), key=lambda s: -bin(s).count("1")):
        vs = [v for v in range(n) if S >> v & 1]
        if S == full:
            for v in vs: C[(S, v)] = Fr(0)
            continue
        idx = {v: i for i, v in enumerate(vs)}
        M = [[Fr(0)] * len(vs) for _ in vs]; b = [Fr(1)] * len(vs)
        for v in vs:
            i = idx[v]; M[i][i] += 1; d = len(adj[v])
            for u in adj[v]:
                if S >> u & 1: M[i][idx[u]] -= Fr(1, d)
                else: b[i] += Fr(1, d) * C[(S | 1 << u, u)]
        for v, x in zip(vs, solve(M, b)): C[(S, v)] = x
    return [C[(1 << s, s)] for s in range(n)]

def main():
    t = time.time(); fails = []; tight = []; count = 0; worst = Fr(0)
    H = lambda k: sum(Fr(1, j) for j in range(1, k + 1))
    for n, gs in sorted(classes().items()):
        if n == 1: continue
        for g in sorted(gs):
            m = len(g); ct = cover_times(n, g); count += 1
            bound = 2 * m * (n - 1)
            for s, x in enumerate(ct):
                if x > bound: fails.append((n, g, s, x, bound))
                r = x / bound
                if r > worst: worst, tight = r, [(n, g, s, x, bound)]
            if m == n * (n - 1) // 2 and any(x != (n - 1) * H(n - 1) for x in ct): fails.append(("complete", n, ct))
            deg = [sum(v in e for e in g) for v in range(n)]
            if m == n - 1 and max(deg) <= 2:   # the path
                ends = [v for v in range(n) if deg[v] == 1]
                if any(ct[v] != (n - 1) ** 2 for v in ends): fails.append(("path", n, ct))
    print(f"{count} connected graphs on 2..{MAXN} vertices (up to isomorphism), every start: cover time <= 2m(n-1)")
    print(f"largest ratio cover/bound = {worst} at n={tight[0][0]}, edges {tight[0][1]}, start {tight[0][2]}: {tight[0][3]} <= {tight[0][4]}")
    for f in fails: print("FAIL", f)
    if fails: sys.exit(1)
    per_n = {n: len(g) for n, g in sorted(classes().items())}
    print(f"classes per n: {per_n}")
    if list(per_n.values()) != [1, 1, 2, 6, 21, 112]: print("FAIL class counts are not OEIS A001349"); sys.exit(1)
    print("PASS")
    print(json.dumps({"states": count, "seconds": round(time.time() - t, 2)}))

if __name__ == "__main__": main()
