# Independent referee check of PAPPUS-JUNK (written from the definitions in opus-light-count.md).
# usage: python3 -I one-not/tools/kill_tests/referee_pappus.py one-not/data/witnesses/pappus_junk_gain.json
import sys, json, itertools
d = json.load(open(sys.argv[1])); n = d['n']; S = [tuple(s) for s in d['sets']]; G = d['gates']; outs = d['outs']
N = 1 << n
def run(notmode):
    # notmode: None real, 0 or 1 constant; returns wire -> list of values over all masks
    W = [[(x >> i) & 1 for x in range(N)] for i in range(n)]
    for g in G:
        if g[0] == 'not': W.append([1 - t for t in W[g[1]]] if notmode is None else [notmode] * N)
        elif g[0] == 'and': W.append([a & b for a, b in zip(W[g[1]], W[g[2]])])
        elif g[0] == 'or': W.append([a | b for a, b in zip(W[g[1]], W[g[2]])])
        else: raise SystemExit('bad op')
    return W
R, C0, C1 = run(None), run(0), run(1)
nots = [k for k, g in enumerate(G) if g[0] == 'not']
print('NOT gates:', len(nots)); assert len(nots) == 1
h = R[G[nots[0]][1]]
ok = all(R[o][x] == (1 if any((x >> p) & 1 for p in S[w]) else 0) for w, o in enumerate(outs) for x in range(N))
print('all 9 sums correct on all %d inputs:' % N, ok); assert ok
print('max |S_i & S_j|:', max(len(set(a) & set(b)) for a, b in itertools.combinations(S, 2)))
print('h(0) =', h[0], '; points with h(e_v)=1:', [v for v in range(n) if h[1 << v]], '; h nonzero:', any(h))
ORS = [n + k for k, g in enumerate(G) if g[0] == 'or']
def wit(g, D, Q):
    """set of zero-points Z over all witnesses of g at (D,Q)"""
    Zs = []
    for S_w in S:
        avail = [p for p in S_w if p not in D]
        if len(avail) < 2: continue
        dm = sum(1 << p for p in D) | sum(1 << p for p in S_w)
        qm = sum(1 << p for p in Q)
        if qm & sum(1 << p for p in S_w): continue   # w not alive at Q
        for Z in range(N):
            if Z & dm or (Z & qm) != qm: continue
            for a, b in itertools.combinations(avail, 2):
                A, B = Z | 1 << a, Z | 1 << b
                if (h[Z] == 0 and C1[g][Z] == 0 and C1[g][A] and C1[g][B]) or \
                   (h[A] and h[B] and C0[g][Z] == 0 and C0[g][A] and C0[g][B]):
                    Zs.append(Z); break
    return Zs
def UC(D, Q): return {g: wit(g, D, Q) for g in ORS if wit(g, D, Q)}
U = UC((), ())
base = sum(len(s) - 1 for s in S)
print('|UC(0,0)| =', len(U), ' base =', base)
print('UC gates (wire ids):', sorted(U))
print('v: gain(x_v:=1) | Lemma-D count #{g: v not in Zall(g)} | cost sum(|S_w|-1) | gain(x_v:=0) | deg')
for v in range(n):
    U1 = UC((), (v,)); g1 = len(set(U) - set(U1))
    ld = sum(1 for g in U if not any((z >> v) & 1 for z in U[g]))
    cost = sum(len(s) - 1 for s in S if v in s)
    U0 = UC((v,), ()); g0 = len(set(U) - set(U0))
    print(v, g1, ld, cost, g0, sum(1 for s in S if v in s))
    assert U1.keys() <= U.keys() and g1 == ld
