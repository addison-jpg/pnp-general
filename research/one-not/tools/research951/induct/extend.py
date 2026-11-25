# Run from the repository root:  ls <circuit .json files> | python3 research/one-not/tools/research951/induct/extend.py
"""(E) Which pure classes lie in SOME pure SDR of the whole system?  Kinds: I1top (Z = top_w), I1 (other maximal Z), I0.
Non-vacuous (pg2: w6's I1 class lies in no SDR).  A kind that is always extendable is a candidate canonical first pick for (M)."""
import sys, json, itertools, collections
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mtest.py')).read(); exec(src[:src.index("def menus_of")])
def kmenus(n, S, G):
    W0 = tables(n, G, 0); W1 = tables(n, G, 1); Wr = tables(n, G, 'real'); P_ = 1 << n
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    out = []
    for R in S:
        Rm = sum(1 << u for u in R); top = (P_ - 1) & ~Rm; rest = [v for v in range(n) if v not in R]
        Minw = [m for m in mint if not m & Rm]; res = []; cls = {}
        if not Minw: res = [0]
        else:
            for k in range(len(rest) + 1):
                for tt in itertools.combinations(rest, k):
                    t = sum(1 << v for v in tt)
                    if all(m & t for m in Minw) and not any((r & t) == r for r in res): res.append(t)
        for t in res:
            C = merges(W1, n, G, R, top & ~t, {u: 1 << u for u in R}); cls.setdefault(C, set()).add('I1top' if t == 0 else 'I1')
        if hb(top):
            per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 2000):
                C = merges(W0, n, G, R, top, {u: ms[i] | 1 << u for i, u in enumerate(R)}); cls.setdefault(C, set()).add('I0')
        out.append(cls)
    return out
def sdr_with(Me, w0, C0):
    order = sorted([v for v in range(len(Me)) if v != w0], key=lambda v: len(Me[v]))
    def rec(i, used):
        if i == len(order): return True
        return any(rec(i + 1, used | C) for C in Me[order[i]] if not used & C)
    return rec(0, C0)
st = collections.Counter(); ex = []
for path in sys.stdin.read().split():
    d = json.load(open(path)); n, S, G = d['n'], d['sets'], d['gates']
    if n > 13: continue
    KM = kmenus(n, S, G); Me = [list(k.keys()) for k in KM]
    for w in range(len(S)):
        if len(KM[w]) < 2: st["sets with 1 class (forced)"] += 1; continue
        st["sets with >= 2 classes"] += 1
        for C, kinds in KM[w].items():
            e = sdr_with(Me, w, C); lab = '+'.join(sorted(kinds))
            st[lab + ' classes'] += 1; st[lab + ' extendable'] += e
            if not e and len(ex) < 8: ex.append((path.split('/')[-1], w, S[w], lab, sorted(C)))
        # per set: is SOME class of each kind extendable?
for k in sorted(st): print('%-28s %d' % (k, st[k]))
for e in ex: print('NOT EXTENDABLE', e)
