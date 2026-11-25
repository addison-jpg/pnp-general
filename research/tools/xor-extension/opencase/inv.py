# Candidate lemma INV: in a circuit of the residual shape whose output changes with x at every y,
#   on side x = 0 the gates H1 and H2 are never both 1, and on side x = 1 they are never both 0.
# Search for a violation (shape + flip only, no minimality condition).  UNSAT = INV holds for (k, r).
# Usage: inv.py k r
import sys, os, time
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..')); sys.path.insert(0, os.path.join(here, '..', 'residual'))
from pysat.solvers import Cadical153
from cegar2 import build, decode
k, r = int(sys.argv[1]), int(sys.argv[2])
cl, V = build(k, r, False)
N = k + 1; x = k; Rr = 1 << N; s1, s2, a, v = V['s1'], V['s2'], V['a'], V['v']
top = [max(abs(l) for c in cl for l in c)]
def nv():
    top[0] += 1; return top[0]
# isH1[j]: gate j is an OR that reads a gate reading x; isH2[j]: gate j is an AND that reads a gate reading x
rdx = []
for i in range(r):
    t = nv(); cl += [[-t, s1[i][x], s2[i][x]], [t, -s1[i][x]], [t, -s2[i][x]]]; rdx.append(t)
isH = {1: [], 2: []}
for j in range(r):
    ts = []
    for i in range(j):
        t = nv(); u = nv()
        cl += [[-u, s1[j][N + i], s2[j][N + i]], [u, -s1[j][N + i]], [u, -s2[j][N + i]]]
        cl += [[-t, rdx[i]], [-t, u], [t, -rdx[i], -u]]; ts.append(t)
    h = nv(); cl.append([-h] + ts)
    for t in ts: cl.append([h, -t])
    h1 = nv(); h2 = nv()
    cl += [[-h1, h], [-h1, -a[j]], [h1, -h, a[j]], [-h2, h], [-h2, a[j]], [h2, -h, -a[j]]]
    isH[1].append(h1); isH[2].append(h2)
# violation: some row with x = 0 where H1 = H2 = 1, or some row with x = 1 where H1 = H2 = 0
viol = []
for row in range(Rr):
    c = (row >> x) & 1
    for j1 in range(r):
        for j2 in range(r):
            if j1 == j2: continue
            t = nv(); viol.append(t)
            cl += [[-t, isH[1][j1]], [-t, isH[2][j2]]]
            cl += [[-t, v[j1][row] if c == 0 else -v[j1][row]], [-t, v[j2][row] if c == 0 else -v[j2][row]]]
cl.append(viol)
t0 = time.time()
with Cadical153(bootstrap_with=cl) as S:
    if S.solve(): print('k', k, 'r', r, 'INV VIOLATED', decode(S.get_model(), V), flush=True)
    else: print('k', k, 'r', r, 'INV holds (UNSAT)', round(time.time() - t0, 1), flush=True)
