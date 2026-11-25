# For each class of 4-variable functions f with C(f) = C(not f) = m (exact sizes from sizes4.txt):
# is there a circuit of the residual shape with m + 3 gates for x XOR f that satisfies the necessary
# conditions M1, N1, N2, N3 (flags ABCDEF of residual/cegar2.py)?  UNSAT = no counterexample for this f.
# Usage: fixed4.py m part nparts [per_instance_seconds]
import sys, os, time, itertools, threading
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..')); sys.path.insert(0, os.path.join(here, '..', 'residual'))
from pysat.solvers import Cadical153
from cegar2 import build, decode
k = 4; R = 16
sz = dict(tuple(map(int, l.split())) for l in open(os.path.join(here, '..', 'sizes4.txt')))
def variants(ft):
    f = [(ft >> r) & 1 for r in range(R)]; res = set()
    for pi in itertools.permutations(range(k)):
        g = [0] * R
        for row in range(R):
            g[sum(((row >> i) & 1) << pi[i] for i in range(k))] = f[row]
        for h in (g, [g[R - 1 - r] for r in range(R)]):
            v = sum(h[r] << r for r in range(R)); res.add(v); res.add(65535 ^ v)
    return res
def depends_on_all(ft):
    return all(any(((ft >> row) & 1) != ((ft >> (row ^ (1 << i))) & 1) for row in range(R)) for i in range(k))
m, part, nparts = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
limit = float(sys.argv[4]) if len(sys.argv) > 4 else 600.0
seen = set(); cls = []
for ft in range(65536):
    if sz[ft] == m and sz[65535 ^ ft] == m and ft not in seen:
        seen |= variants(ft)
        if depends_on_all(ft): cls.append(ft)
r = m + 3
base, V = build(k, r, True, 'ABCDEF')
for w in range(k):
    base.append([s[i][w] for i in range(r) for s in (V['s1'], V['s2'])])
out = V['v'][r - 1]
for idx, ft in enumerate(cls):
    if idx % nparts != part: continue
    S = Cadical153(bootstrap_with=base)
    for row in range(32):
        bit = ((ft >> (row & 15)) & 1) ^ (row >> 4)
        S.add_clause([out[row] if bit else -out[row]])
    t = time.time(); timer = threading.Timer(limit, S.interrupt); timer.start()
    res = S.solve_limited(expect_interrupt=True); timer.cancel()
    print('f', ft, 'm', m, 'r', r, {True: 'SAT ' + str(decode(S.get_model(), V)) if res else '', False: 'UNSAT', None: 'TIMEOUT'}[res],
          round(time.time() - t, 1), 'class', idx, 'of', len(cls), flush=True)
    S.delete()
