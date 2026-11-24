# Conjecture C3_k on circuits with NO gate-saving rewiring (MinCE.no_rewire as a property of the circuit) and every gate read.
# Serves README items L2, C2, C3.  Corpus: every circuit file under one-not/ with n <= NMAX and one NOT gate, plus
# f2lib.randgen(seed, count).  For each rewire-irreducible circuit: depth (c3_allq.depths) at every cube with base > 0.
# Run: python3 -I one-not/tools/kill_tests/c3_norewire_corpus.py [NMAX=9] [seed=1] [count=3000] [cap=3] [reduce]
# With 'reduce': every circuit is first reduced greedily by gate-saving rewirings; the distinct irreducible results are tested.
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f2lib as L, c3_allq as A
def find_rewire(c, rng=None):
    # None if an unread gate exists or a gate-saving rewiring exists returns (G2, live); 'ok' if irreducible
    n = c['n']; G = c['G']; outs = c['outs']; FULL = c['FULL']; X = c['X']; N = n + len(G)
    want = [c['W'][o] for o in outs]
    def live(G2):
        seen = set(); st = list(outs)
        while st:
            i = st.pop()
            if i < n or i in seen: continue
            seen.add(i); st += G2[i - n][1:]
        return seen
    if len(live(G)) < len(G): return (G, live(G))   # an unread gate: delete it
    cand = [(k, pos, f) for k, g in enumerate(G) for pos in range(1, len(g)) for f in range(N)]
    if rng: rng.shuffle(cand)
    for k, pos, f in cand:
        g = G[k]
        if True:
            if True:
                if f == g[pos] or f == n + k: continue
                G2 = list(G); G2[k] = list(g); G2[k][pos] = f
                lv = live(G2)
                if len(lv) == len(G): continue        # no gate saved
                W = {}; state = {}; ok = True
                def get(i):
                    if i < n: return X[i]
                    if i in W: return W[i]
                    if state.get(i): raise RecursionError
                    state[i] = 1; h = G2[i - n]
                    v = FULL ^ get(h[1]) if h[0] == 'not' else (get(h[1]) & get(h[2]) if h[0] == 'and' else get(h[1]) | get(h[2]))
                    W[i] = v; return v
                try:
                    if all(get(o) == t for o, t in zip(outs, want)): return (G2, lv)
                except RecursionError: pass
    return 'ok'
def irreducible(c): return find_rewire(c) == 'ok'
def reduce(c, rng=None):
    # greedy: apply gate-saving rewirings (and delete unread gates) until none is left; returns the irreducible circuit
    while True:
        r = find_rewire(c, rng)
        if r == 'ok': return c
        G2, lv = r; n = c['n']; order = []; seen = set()
        def visit(i):
            if i < n or i in seen: return
            seen.add(i)
            for j in G2[i - n][1:]: visit(j)
            order.append(i)
        for o in c['outs']: visit(o)
        ren = {v: v for v in range(n)}
        for j, i in enumerate(order): ren[i] = n + j
        c2 = L.mk(c['name'], n, c['S'], [[G2[i - n][0]] + [ren[x] for x in G2[i - n][1:]] for i in order], [ren[o] for o in c['outs']], need_not=False)
        assert c2 is not None
        c = c2
if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'random':
    # random reduction orders from one circuit: python3 -I c3_norewire_corpus.py random FILE.json runs [seed]
    import json, random
    d = json.load(open(sys.argv[2])); runs = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    c0 = L.mk(d.get('name', ''), d['n'], d['sets'], d['gates'], d['outs'], need_not=False); seen = {}; tot = collections.Counter(); nr = 0
    for _ in range(runs):
        c = reduce(c0, rng); key = str((c['G'], c['outs']))
        if key in seen: continue
        h, ha, worst, ms = A.depths(c, 3); seen[key] = 1; tot.update(h); nr += any(g[0] == 'not' for g in c['G'])
        print('irreducible end circuit: gates', len(c['G']), 'NOT read' if any(g[0] == 'not' for g in c['G']) else 'NOT unread', 'depth histogram over all cubes', dict(h), 'min slack', ms, flush=True)
    print(sys.argv[2], 'runs', runs, 'distinct irreducible end circuits', len(seen), 'with the NOT gate read', nr, 'depth histogram over all their cubes', dict(tot))
elif __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9; seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    cnt = int(sys.argv[3]) if len(sys.argv) > 3 else 3000; cap = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    CS = L.corpus(NMAX) + (L.randgen(seed, cnt) if cnt else [])
    tot = collections.Counter(); irr = 0; cubes = 0; deep = []; notread = 0
    red = len(sys.argv) > 5 and sys.argv[5] == 'reduce'; seen = set()
    for c in CS:
        if red:
            c = reduce(c); key = str((c['n'], c['S'], c['G'], c['outs']))
            if key in seen: continue
            seen.add(key)
        elif not irreducible(c): continue
        irr += 1; notread += any(g[0] == 'not' for g in c['G'])
        h, ha, worst, ms = A.depths(c, cap); tot.update(h); cubes += sum(h.values())
        if any(k != 1 for k in h): deep.append((c['name'], dict(h), worst))
    print('circuits', len(CS), '| reduced by gate-saving rewirings, distinct:' if red else '| with every gate read and no gate-saving rewiring:', irr, '| of these with the NOT gate still read:', notread, '| cubes with base > 0:', cubes)
    print('depth histogram over those cubes:', dict(sorted(tot.items(), key=str)))
    for x in deep[:20]: print('  depth > 1:', x)
