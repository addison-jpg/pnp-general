# Local-constraint search, plus: every y-input is read by some gate (WLOG when f depends on all k variables).
import sys, time
from pysat.solvers import Cadical153
from cegar2 import build, decode
k, r, fl = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
cl, V = build(k, r, True, fl)
for w in range(k):
    cl.append([s[i][w] for i in range(r) for s in (V['s1'], V['s2'])])
t = time.time()
with Cadical153(bootstrap_with=cl) as S:
    if S.solve():
        m = S.get_model(); ms = set(l for l in m if l > 0)
        f = [1 if V['v'][r-1][row] in ms else 0 for row in range(1 << k)]
        print('k', k, 'r', r, fl, 'allread SAT', round(time.time() - t), 'f', f, decode(m, V), flush=True)
    else: print('k', k, 'r', r, fl, 'allread UNSAT', round(time.time() - t), flush=True)
