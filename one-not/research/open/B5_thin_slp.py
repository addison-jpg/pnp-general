"""B5: S3(b) in Hall form for EVERY circuit (any size, any number of NOT gates) on a family W, by SAT on functions.

Relaxation (B5_flip_hall.md, section 4). Let K = the union of C(w), w in W (flip classes serving W). A wire whose class is not in K
is W-thin: |D| <= 1 at every zero point of every set of W. The first wire of each class in K is an AND or OR gate whose two inputs
are earlier wires: each is W-thin, a constant, or +- the first wire of an earlier class in K. Every output OR(S_w) is +- such a
first wire. So a Hall violation on W (|K| <= base(W) - 1) gives a straight-line program of K = base(W) - 1 lines
F_i = L_i op_i R_i over arbitrary W-thin functions, with every output among +-F_i. UNSAT => Hall holds on W for all circuits.
Usage: python3 -I B5_thin_slp.py SYSTEM [maxW] [--control] [--free=K] [--iso]
  --control allows base(W) lines (must be SAT); --free=K adds K inputs outside every set; --iso tests one family per
  isomorphism class (relabelling of the n inputs)."""
import sys, itertools, time
from pysat.solvers import Solver

SYSTEMS = {
    'two3':  (5, [(0, 1, 2), (0, 3, 4)]),
    'dis3':  (6, [(0, 1, 2), (3, 4, 5)]),
    'tri3':  (6, [(0, 1, 3), (1, 2, 4), (0, 2, 5)]),
    'star3': (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6)]),
    'pasch': (6, [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]),
    'fano':  (7, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]),
    'star44': (7, [(0, 1, 2, 3), (0, 4, 5, 6)]),
    'dis44': (8, [(0, 1, 2, 3), (4, 5, 6, 7)]),
    'two43': (6, [(0, 1, 2, 3), (0, 4, 5)]),
    'dis43': (7, [(0, 1, 2, 3), (4, 5, 6)]),
    'tri4':  (6, [(0, 1, 3, 4), (1, 2, 5), (0, 2)]),
    'q4':    (6, [(0, 1, 2, 3), (0, 4, 5), (1, 4), (2, 5)]),
    'star5': (9, [(0, 1, 2, 3, 4), (0, 5, 6, 7, 8)]),
    'one4':  (4, [(0, 1, 2, 3)]),
}

def solve(n, W, extra=0):
    N = 1 << n; K = sum(len(S) - 1 for S in W) - 1 + extra
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    cl = []
    zeros = [[Z for Z in range(N) if not any(Z >> u & 1 for u in S)] for S in W]
    def thin(T, guard):
        for S, zs in zip(W, zeros):
            for Z in zs:
                for u, v in itertools.combinations(S, 2):
                    zu, zv = Z | 1 << u, Z | 1 << v
                    cl.append([-guard, T[Z], -T[zu], -T[zv]]); cl.append([-guard, -T[Z], T[zu], T[zv]])
    def eqsel(p, X, Yv, s):
        for x in range(N):
            if s == 0: cl.append([-p, -X[x], Yv[x]]); cl.append([-p, X[x], -Yv[x]])
            else: cl.append([-p, -X[x], -Yv[x]]); cl.append([-p, X[x], Yv[x]])
    F = []
    for i in range(K):
        Fi = [new() for _ in range(N)]; op = new()
        sides = []
        for _ in range(2):
            X = [new() for _ in range(N)]; g = new(); sel = [g]; thin(X, g)
            for j in range(i):
                for s in (0, 1):
                    p = new(); sel.append(p); eqsel(p, X, F[j], s)
            cl.append(sel); sides.append(X)
        L, R = sides
        for x in range(N):  # Fi = op ? L|R : L&R
            cl.append([-op, -Fi[x], L[x], R[x]]); cl.append([-op, Fi[x], -L[x]]); cl.append([-op, Fi[x], -R[x]])
            cl.append([op, Fi[x], -L[x], -R[x]]); cl.append([op, -Fi[x], L[x]]); cl.append([op, -Fi[x], R[x]])
        F.append(Fi)
    for S in W:
        o = [int(any(x >> u & 1 for u in S)) for x in range(N)]
        sel = []
        for i in range(K):
            for s in (0, 1):
                p = new(); sel.append(p)
                for x in range(N):
                    lit = F[i][x] if (o[x] ^ s) else -F[i][x]
                    cl.append([-p, lit])
        cl.append(sel)
    with Solver(name='cd15', bootstrap_with=cl) as sv:
        return sv.solve()

if __name__ == '__main__':
    name = sys.argv[1]; n, sets = SYSTEMS[name]
    ctl = '--control' in sys.argv
    iso = '--iso' in sys.argv
    for a in sys.argv:
        if a.startswith('--free='): n += int(a[7:])
    seen = set()
    def canon(W):
        return min(tuple(sorted(tuple(sorted(p[u] for u in S)) for S in W)) for p in itertools.permutations(range(n)))
    args = [a for a in sys.argv[2:] if not a.startswith('--')]
    maxw = int(args[0]) if args else len(sets)
    tot = sat = 0
    for r in range(1, min(maxw, len(sets)) + 1):
        for W in itertools.combinations(sets, r):
            if sum(len(S) - 1 for S in W) <= r and not ctl: continue  # only pairs: outputs alone, Hall trivial
            if iso:
                cf = canon(W)
                if cf in seen: continue
                seen.add(cf)
            t0 = time.time(); res = solve(n, list(W), 1 if ctl else 0); tot += 1; sat += bool(res)
            print(name, 'n=%d' % n, W, 'SAT' if res else 'UNSAT', '%.1fs' % (time.time() - t0), flush=True)
    print(name, 'control' if ctl else 'violation', 'subfamilies', tot, 'SAT', sat, flush=True)
