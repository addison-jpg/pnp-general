# nf.py (scaffold, desktop Coord 12:48): "MinCE normal form" violations R1-R6 of a one-NOT circuit.
# R1 gate constant (real); R2 two gates with equal real function; R3 gate equal to an input; R4 unread non-output gate;
# R5 inessential NOT; R6 N-dependent gate whose real function equals its C0 or C1 function.
import sys, json
D = '/tmp/claude-0/-home-user/dbc7162d-d362-5361-8133-bb93548aca7c/scratchpad/f15'
sys.path.insert(0, D); sys.path.insert(0, D + '/heavy')
from mfrac import tables
from killtests import tables_force

def nf(c):
    n = c['n']; R = 1 << n; full = (1 << R) - 1; T = tables(c); T0 = tables_force(c, 0); T1 = tables_force(c, 1); s = len(c['gates'])
    W = range(n, n + s); v = {}
    v['R1'] = [g for g in W if T[g] in (0, full)]
    seen = {}; v['R2'] = []
    for g in W:
        if T[g] in seen: v['R2'].append([seen[T[g]], g])
        else: seen[T[g]] = g
    v['R3'] = [[g, next(i for i in range(n) if T[i] == T[g])] for g in W if any(T[i] == T[g] for i in range(n))]
    read = {a for gg in c['gates'] for a in gg[1:]}; v['R4'] = [g for g in W if g not in read and g not in c['outs']]
    v['R5'] = [] if (any(T0[o] != T[o] for o in c['outs']) and any(T1[o] != T[o] for o in c['outs'])) else ['NOT inessential']
    p = [k for k, g in enumerate(c['gates']) if g[0] == 'not']; dep = {n + k for k in p}
    for k, g in enumerate(c['gates']):
        if g[0] != 'not' and any(a in dep for a in g[1:]): dep.add(n + k)
    v['R6'] = [g for g in sorted(dep) if c['gates'][g - n][0] != 'not' and (T[g] == T0[g] or T[g] == T1[g])]
    return {k: x for k, x in v.items()}

if __name__ == '__main__':
    for fn in sys.argv[1:]:
        B = json.load(open(fn))
        items = B.items() if isinstance(B, dict) and 'gates' not in B else [(fn, B)]
        for name, c in items:
            r = nf(c); print(name, 's', len(c['gates']), {k: (len(x), x[:4]) for k, x in r.items()})
