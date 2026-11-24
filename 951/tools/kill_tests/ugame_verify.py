"""cTAHG referee (2026-11-24): referee check of Theorem G on the barrier suite: ugame.solve, then INDEPENDENT verification of the selected systems
(validity, Theorem U certificates, union-find classes in the lift of size d_w, pairwise disjoint).
Usage (from 951/): python3 -I tools/kill_tests/ugame_verify.py FILE.json ..."""
import sys, json, time
import numpy as np
sys.path.insert(0, 'tools/kill_tests')
import ugame

def lifted(d):
    n = d['n']; N = n + 1; P = 1 << N; idx = np.arange(P, dtype=np.int64)
    W = [((idx >> i) & 1).astype(bool) for i in range(n)]
    y = ((idx >> n) & 1).astype(bool)
    for g in d['gates']:
        if g[0] == 'not': W.append(y.copy())
        elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
        else: W.append(W[g[1]] | W[g[2]])
    return N, W

def run_class(d, W, S, zeta, atoms):
    n = d['n']; par = list(range(len(atoms)))
    def f(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    M = []
    for k in range(len(d['gates'])):
        i = n + k
        if W[i][zeta]: continue
        tr = [j for j, a in enumerate(atoms) if W[i][a]]
        roots = sorted({f(j) for j in tr})
        if len(roots) > 1:
            for r in roots[1:]: par[r] = roots[0]
            M.append(i)
    return M

def check(path):
    d = json.load(open(path)); n = d['n']; S = d['sets']; outs = d['outs']
    if sum(g[0] == 'not' for g in d['gates']) != 1: return path, 'skip'
    t0 = time.time()
    N, W = lifted(d)
    O = [W[o].astype(np.int8).tolist() for o in outs]
    sol = ugame.solve(N, S, O)
    if sol is None:
        return path.split('/')[-1], dict(n=n, s=len(d['gates']), base=sum(len(R) - 1 for R in S), ugame='LOST', sec=round(time.time() - t0, 1))
    cls = {}; ok = True; msgs = []
    for w, (z, atoms) in sol.items():
        if W[outs[w]][z] or len(atoms) != len(S[w]) or not all(W[outs[w]][a] for a in atoms): ok = False; msgs.append('invalid %d' % w)
        for a in range(len(atoms)):
            for b in range(a + 1, len(atoms)):
                if (atoms[a] & atoms[b]) & ~z: ok = False; msgs.append('sep %d' % w)
        cls[w] = run_class(d, W, S[w], z, atoms)
        if len(cls[w]) != len(S[w]) - 1: ok = False; msgs.append('size %d' % w)
    for w in sol:
        for v in sol:
            if w < v:
                cw = sum(1 for a in sol[w][1] if a & ~sol[v][0]) <= 1
                cv = sum(1 for a in sol[v][1] if a & ~sol[w][0]) <= 1
                if not (cw or cv): ok = False; msgs.append('cert %d %d' % (w, v))
                if set(cls[w]) & set(cls[v]): ok = False; msgs.append('overlap %d %d' % (w, v))
    U = set().union(*cls.values())
    return path.split('/')[-1], dict(n=n, s=len(d['gates']), base=sum(len(R) - 1 for R in S), ugame='WON',
                                     verified=ok, msgs=msgs[:4], union=len(U), sec=round(time.time() - t0, 1))

for p in sys.argv[1:]:
    try:
        print(*check(p), flush=True)
    except Exception as e:
        print(p, 'ERROR', repr(e)[:200], flush=True)
