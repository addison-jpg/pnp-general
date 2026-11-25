# Enumerate every function f on k variables (up to permuting variables and replacing f(y) by
# f(not y)) for which x XOR f has a circuit of the residual shape with exactly r gates, and compare
# r with min(C(f), C(not f)) from the exact size tables.  No local (minimality) condition is used:
# only the residual shape and "the output changes with x at every y".
# Usage: enum_shape.py k r [outH] [budget_seconds]
#   outH: additionally require that the output gate is H1 or H2 (the sole reader of G1 or of G2).
#   outZ: additionally require that the output gate is neither H1 nor H2.
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'residual'))
from pysat.solvers import Cadical153
from cegar2 import build, decode, variants

def main():
    k, r = int(sys.argv[1]), int(sys.argv[2])
    outH = 'outH' in sys.argv
    budget = float(sys.argv[-1]) if sys.argv[-1].replace('.', '').isdigit() and len(sys.argv) > 3 else 600.0
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    sz = dict(tuple(map(int, l.split())) for l in open(os.path.join(base, 'sizes%d.txt' % k)))
    full = (1 << (1 << k)) - 1
    cl, V = build(k, r, False)
    N = k + 1; x = k
    if outH:
        # the output gate reads a gate that reads x
        s1, s2 = V['s1'], V['s2']; lits = []
        top = max(abs(l) for c in cl for l in c)
        for i in range(r - 1):
            top += 1; t = top; lits.append(t)
            # t -> gate i reads x and the output gate reads gate i
            cl.append([-t, s1[i][x], s2[i][x]])
            cl.append([-t, s1[r - 1][N + i], s2[r - 1][N + i]])
        cl.append(lits)
    if 'outZ' in sys.argv:
        # the output gate reads no gate that reads x
        s1, s2 = V['s1'], V['s2']
        for i in range(r - 1):
            for sa in (s1[i][x], s2[i][x]):
                for sb in (s1[r - 1][N + i], s2[r - 1][N + i]):
                    cl.append([-sa, -sb])
    S = Cadical153(bootstrap_with=cl); R = 1 << k; out = V['v'][r - 1]
    # f is not constant
    S.add_clause([out[row] for row in range(R)]); S.add_clause([-out[row] for row in range(R)])
    t0 = time.time(); worst = None; nclass = 0; hist = {}
    while True:
        if time.time() - t0 > budget:
            print('k', k, 'r', r, 'outH' if outH else ('outZ' if 'outZ' in sys.argv else ''), 'TIMEOUT after', nclass, 'classes; least r - min so far', worst, flush=True); return
        if not S.solve(): break
        m = set(l for l in S.get_model() if l > 0)
        f = tuple(1 if out[row] in m else 0 for row in range(R))
        ft = sum(f[row] << row for row in range(R))
        a, b = sz[ft], sz[full ^ ft]
        a = 99 if a < 0 else a; b = 99 if b < 0 else b   # -1 in sizes4.txt means more than 8 gates
        d = r - min(a, b); nclass += 1; hist[d] = hist.get(d, 0) + 1
        if worst is None or d < worst[0]:
            worst = (d, ft, (a, b), decode(m, V)); print('new least r - min:', worst, flush=True)
        for g in variants(f, k):
            S.add_clause([(-out[row] if g[row] else out[row]) for row in range(R)])
    print('k', k, 'r', r, 'outH' if outH else ('outZ' if 'outZ' in sys.argv else ''), 'DONE classes', nclass, 'histogram of r - min(C(f),C(not f)):',
          sorted(hist.items()), 'least:', worst, 'time', round(time.time() - t0), flush=True)
main()
