"""Pure menus (I1 at maximal Z off S_w; I0 at top_w with minterm atoms), #pure SDRs, and unit-propagation trace."""
import sys, json, itertools, functools
sys.argv = ['x', 'one-not', '13']
src = open('one-not/tools/kill_tests/canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
for path in sys.stdin.read().split():
    d = json.load(open(path)); n, S, G, outs = d['n'], d['sets'], d['gates'], d['outs']
    Wr = tables(n, G, 'real'); W0 = tables(n, G, 0); W1 = tables(n, G, 1); P_ = 1 << n
    assert all(Wr[o] == functools.reduce(lambda a, b: a | b, [Wr[u] for u in R], 0) for o, R in zip(outs, S))
    ni = n + [k for k, g in enumerate(G) if g[0] == 'not'][0]; h = Wr[G[ni - n][1]]; hb = lambda x: (h >> x) & 1
    mint = [x for x in range(P_) if hb(x) and not any(hb(x & ~(1 << v)) for v in range(n) if x >> v & 1)]
    base = sum(len(R) - 1 for R in S)
    menus = []
    for w, R in enumerate(S):
        Rm = sum(1 << u for u in R); top = (P_ - 1) & ~Rm; rest = [v for v in range(n) if v not in R]
        Minw = [m for m in mint if not m & Rm]
        # I1 points via (a): top minus minimal transversals of Min_w
        cls = {}
        def trans_min():
            if not Minw: yield 0; return
            res = []
            for k in range(len(rest) + 1):
                for tt in itertools.combinations(rest, k):
                    t = sum(1 << v for v in tt)
                    if all(m & t for m in Minw) and not any((r & t) == r for r in res): res.append(t); yield t
        for t in trans_min():
            M = merges(W1, n, G, R, top & ~t, {u: 1 << u for u in R}); cls.setdefault(M, set()).add('I1')
        if hb(top):
            per = [[m for m in mint if (m & Rm) & ~(1 << u) == 0] for u in R]
            for ms in itertools.islice(itertools.product(*per), 3000):
                M = merges(W0, n, G, R, top, {u: ms[i] | 1 << u for i, u in enumerate(R)}); cls.setdefault(M, set()).add('I0')
        menus.append(cls)
    sols = []
    def rec(i, used, pick):
        if i == len(S): sols.append(list(pick)); return
        for M in menus[i]:
            if not (M & used): pick.append(M); rec(i + 1, used | M, pick); pick.pop()
    rec(0, frozenset(), [])
    print('##', path.split('/')[-1], f's={len(G)} base={base} h-minterms={[ [v for v in range(n) if m>>v&1] for m in mint]} #pureSDR={len(sols)}')
    for w in range(len(S)):
        print(f'  w{w} {S[w]} type {"A" if hb((P_-1)&~sum(1<<u for u in S[w])) else "B"}:', '; '.join(f'{sorted(M)} {"/".join(sorted(t))}' for M, t in menus[w].items()))
    # unit propagation: repeatedly fix sets with one remaining class, delete conflicting classes elsewhere
    rem = [set(m) for m in menus]; fixed = {}; rounds = 0
    while True:
        new = [w for w in range(len(S)) if w not in fixed and len(rem[w]) == 1]
        if not new: break
        rounds += 1
        for w in new:
            M = next(iter(rem[w])); fixed[w] = M
            for v in range(len(S)):
                if v != w and v not in fixed: rem[v] = {N for N in rem[v] if not (N & M)}
    print(f'  unit propagation: {rounds} rounds, fixed {len(fixed)}/{len(S)}, sets left with 0 classes: {[w for w in range(len(S)) if not rem[w]]}, open: {[ (w,len(rem[w])) for w in range(len(S)) if w not in fixed and rem[w]]}')
