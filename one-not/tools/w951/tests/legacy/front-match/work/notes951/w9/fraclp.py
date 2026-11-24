# FracMatch LP: each set w mixes over its maximal counted sets C_{w,j} (from allsys.menus) with weights lam_{w,j};
# within C_{w,j} it spreads d_w*lam_{w,j} units, at most lam_{w,j} per gate (= convex comb. of (d_w)-subsets).
# Minimise L = max gate load. FracMatch holds iff L <= 1.  Usage: fraclp.py circuit.json|circuits.jsonl [cone]
import sys, json, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'w8'))
from allsys import menus
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def fraclp(c, coneonly=False, M=None):
    if M is None: M = menus(c, coneonly)
    dem = [len(s)-1 for s in c['sets']]
    var = {}; 
    def v(k):
        if k not in var: var[k] = len(var)
        return var[k]
    v('L')
    sysl = [(w, j, sorted(C)) for w, m in enumerate(M) for j, C in enumerate(m)]
    for w, j, C in sysl:
        v(('lam', w, j))
        for g in C: v(('y', w, j, g))
    gates = sorted({g for _, _, C in sysl for g in C})
    eq = []; ub = []
    for w, m in enumerate(M): eq.append(({v(('lam', w, j)): 1 for j in range(len(m))}, 1))
    for w, j, C in sysl:
        r = {v(('y', w, j, g)): 1 for g in C}; r[v(('lam', w, j))] = -dem[w]; eq.append((r, 0))
        for g in C: ub.append(({v(('y', w, j, g)): 1, v(('lam', w, j)): -1}, 0))
    for g in gates:
        r = {v(('y', w, j, g)): 1 for w, j, C in sysl if g in C}; r[v('L')] = -1; ub.append((r, 0))
    def mat(rows):
        A = lil_matrix((len(rows), len(var))); b = np.zeros(len(rows))
        for i, (r, bb) in enumerate(rows):
            for k, a in r.items(): A[i, k] = a
            b[i] = bb
        return A.tocsr(), b
    Ae, be = mat(eq); Au, bu = mat(ub); cost = np.zeros(len(var)); cost[0] = 1
    res = linprog(cost, A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be, bounds=[(0, None)]*len(var), method='highs')
    lam = {(k[1], k[2]): res.x[i] for k, i in var.items() if k != 'L' and k[0] == 'lam' and res.x[i] > 1e-9}
    return res.fun, lam, M
if __name__ == '__main__':
    cone = len(sys.argv) > 2
    f = sys.argv[1]
    cs = [json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    worst = None
    for i, c in enumerate(cs):
        L, lam, M = fraclp(c, cone)
        if worst is None or L > worst[0]: worst = (L, i)
        if len(cs) <= 5:
            print(f, i, 'L* =', round(L, 6), 'menu sizes', [len(m) for m in M], 'support', {k: round(x, 3) for k, x in lam.items()})
    print('circuits', len(cs), 'worst L*', round(worst[0], 6), 'at', worst[1], 'FRACMATCH FAILS' if worst[0] > 1 + 1e-7 else 'ok')
