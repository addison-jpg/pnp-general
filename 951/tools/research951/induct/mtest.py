# Run from the repository root:  ls <circuit .json files> | python3 951/tools/research951/induct/mtest.py
"""Unconditional test of the missing lemma (M) of research-induction-draft.md:
for every subfamily F (|F| >= 2) of a correct one-NOT circuit's sets, with NO tight proper subfamily
(tight(G): |∪ of all pure classes of G| == base(G)), is there a class C of some w ∈ F such that every v ∈ F - w keeps a class
disjoint from C?  Pure menus as in menus.py."""
import sys, json, itertools, functools
sys.argv = ['x', '951', '13']
src = open('951/tools/kill_tests/canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
def menus_of(n, S, G):
    W0 = tables(n, G, 0); W1 = tables(n, G, 1); Wr = tables(n, G, 'real'); P_ = 1 << n
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    out = []
    for R in S:
        Rm = sum(1 << u for u in R); top = (P_ - 1) & ~Rm; rest = [v for v in range(n) if v not in R]
        Minw = [m for m in mint if not m & Rm]; cls = set(); res = []
        if not Minw: res = [0]
        else:
            for k in range(len(rest) + 1):
                for tt in itertools.combinations(rest, k):
                    t = sum(1 << v for v in tt)
                    if all(m & t for m in Minw) and not any((r & t) == r for r in res): res.append(t)
        for t in res: cls.add(merges(W1, n, G, R, top & ~t, {u: 1 << u for u in R}))
        if hb(top):
            per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 2000):
                cls.add(merges(W0, n, G, R, top, {u: ms[i] | 1 << u for i, u in enumerate(R)}))
        out.append(cls)
    return out
tot = {'families': 0, 'no tight proper subfamily': 0, 'M holds': 0, 'M fails': 0}; fails = []
for path in sys.stdin.read().split():
    d = json.load(open(path)); n, S, G, outs = d['n'], d['sets'], d['gates'], d['outs']
    if n > 13: continue
    Me = menus_of(n, S, G); base = [len(R) - 1 for R in S]
    U = lambda F: frozenset().union(*[M for w in F for M in Me[w]])
    tight = lambda F: len(U(F)) == sum(base[w] for w in F)
    for k in range(2, min(len(S), 6) + 1):
        for F in itertools.combinations(range(len(S)), k):
            tot['families'] += 1
            if any(tight(G2) for j in range(1, k) for G2 in itertools.combinations(F, j)): continue
            tot['no tight proper subfamily'] += 1
            ok = any(all(any(not (N & C) for N in Me[v]) for v in F if v != w) for w in F for C in Me[w])
            tot['M holds' if ok else 'M fails'] += 1
            if not ok and len(fails) < 5: fails.append((path.split('/')[-1], [S[w] for w in F], [[sorted(C) for C in Me[w]] for w in F]))
print(tot); [print('FAIL', f) for f in fails]
