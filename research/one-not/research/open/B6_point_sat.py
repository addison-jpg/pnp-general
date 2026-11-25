"""B6: the single-point relaxation of the thin-basis lemma (B6_thin_basis.md s2), by SAT.

At the common zero point 0 of all sets, sens(F) = {u : F(e_u) != F(0)}. For F = L op R (AND/OR, any signs)
sens(F) is sens(L) | sens(R), sens(L) & sens(R), sens(L) - sens(R) or sens(R) - sens(L) (which one depends on L(0), R(0)).
A W-thin leaf has sens meeting every set in <= 1 point; OR(S_w) has sens exactly S_w. So a thin SLP with K lines gives a
"set program": K lines X_i = A op B (op in the four above), A, B a partial transversal or an earlier line, every S_w
among the X_i. UNSAT at K = base-1 => the thin-basis lemma holds for W. SAT says nothing (relaxation).
Usage: python3 -I B6_point_sat.py NAME [--control]"""
import sys, itertools, time
from pysat.solvers import Solver

def grid(q):
    rows = [tuple(q * i + j for j in range(q)) for i in range(q)]
    cols = [tuple(q * i + j for i in range(q)) for j in range(q)]
    return (q * q, rows + cols)
def ag3():
    P = [(x, y) for x in range(3) for y in range(3)]; idx = {p: i for i, p in enumerate(P)}; L = set()
    for p in P:
        for d in [(0, 1), (1, 0), (1, 1), (1, 2)]:
            L.add(tuple(sorted(idx[((p[0] + k * d[0]) % 3, (p[1] + k * d[1]) % 3)] for k in range(3))))
    return (9, sorted(L))
def pg3():
    pts = []
    for v in itertools.product(range(3), repeat=3):
        if any(v) and v[[i for i in range(3) if v[i]][0]] == 1: pts.append(v)
    L = [tuple(i for i, p in enumerate(pts) if sum(a * b for a, b in zip(p, l)) % 3 == 0) for l in pts]
    return (13, L)
SYSTEMS = {
    'fano': (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]),
    'two5': (9, [(0, 1, 2, 3, 4), (0, 5, 6, 7, 8)]),
    'dis5': (10, [(0, 1, 2, 3, 4), (5, 6, 7, 8, 9)]),
    'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),
    'grid3': grid(3), 'grid4': grid(4), 'ag3': ag3(), 'pg3': pg3(),
}

def solve(n, W, K):
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    cl = []; X = []
    for i in range(K):
        sides = []
        for _ in range(2):
            A = [new() for _ in range(n)]; g = new(); sel = [g]
            for S in W:
                for u, v in itertools.combinations(S, 2): cl.append([-g, -A[u], -A[v]])
            for j in range(i):
                p = new(); sel.append(p)
                for u in range(n): cl.append([-p, -A[u], X[j][u]]); cl.append([-p, A[u], -X[j][u]])
            cl.append(sel); sides.append(A)
        A, B = sides; F = [new() for _ in range(n)]; o = [new() for _ in range(4)]
        cl.append(o)
        for u in range(n):
            a, b, f = A[u], B[u], F[u]
            # union
            cl += [[-o[0], -f, a, b], [-o[0], f, -a], [-o[0], f, -b]]
            # intersection
            cl += [[-o[1], f, -a, -b], [-o[1], -f, a], [-o[1], -f, b]]
            # A - B
            cl += [[-o[2], -f, a], [-o[2], -f, -b], [-o[2], f, -a, b]]
            # B - A
            cl += [[-o[3], -f, b], [-o[3], -f, -a], [-o[3], f, -b, a]]
        X.append(F)
    for S in W:
        sel = []
        for i in range(K):
            p = new(); sel.append(p)
            for u in range(n): cl.append([-p, X[i][u] if u in S else -X[i][u]])
        cl.append(sel)
    with Solver(name='cd15', bootstrap_with=cl) as sv:
        return sv.solve()

if __name__ == '__main__':
    name = sys.argv[1]; n, W = SYSTEMS[name]; base = sum(len(S) - 1 for S in W)
    K = base if '--control' in sys.argv else base - 1
    t0 = time.time(); r = solve(n, W, K)
    print(name, 'n=%d sets=%d base=%d lines=%d' % (n, len(W), base, K), 'SAT' if r else 'UNSAT', '%.1fs' % (time.time() - t0), flush=True)
