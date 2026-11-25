"""cTAHG 2026-11-24. Local rewiring test (desktop Coord's R7-REWIRE, generalised to every edge): replace input `pos` of gate wire r by an
existing wire f not in desc(r); keep it if all outputs stay correct; report rewires after which some gate is unread
(a gate saved, no new NOT) -- each such rewire contradicts minimality.
python3 -I research/one-not/tools/kill_tests/rewire_r6.py FILE.json ..."""
import sys, json
import numpy as np

def run(path):
    d = json.load(open(path)); n = d['n']; G = [list(g) for g in d['gates']]; outs = d['outs']; S = d['sets']; P = 1 << n
    idx = np.arange(P, dtype=np.int64)
    want = []
    for R in S:
        t = np.zeros(P, bool)
        for u in R: t |= ((idx >> u) & 1).astype(bool)
        want.append(t)
    def evalc(gates):
        # topological evaluation (gates may reference later wires after rewiring)
        N = n + len(gates); val = [None] * N
        for i in range(n): val[i] = ((idx >> i) & 1).astype(bool)
        state = [0] * N
        def get(i):
            if val[i] is not None: return val[i]
            if state[i] == 1: raise ValueError('cycle')
            state[i] = 1
            g = gates[i - n]
            if g[0] == 'not': v = ~get(g[1])
            elif g[0] == 'and': v = get(g[1]) & get(g[2])
            else: v = get(g[1]) | get(g[2])
            val[i] = v; state[i] = 2
            return v
        return [get(o) for o in outs], get
    def desc(r):
        ds = {r}; changed = True
        while changed:
            changed = False
            for k, g in enumerate(G):
                i = n + k
                if i not in ds and any(j in ds for j in g[1:]):
                    ds.add(i); changed = True
        return ds
    def readers(gates):
        rd = set()
        for g in gates: rd.update(g[1:])
        return rd
    Nw = [n + k for k, g in enumerate(G) if g[0] == 'not'][0]
    found = []; tried = 0; correct = 0
    for k, g in enumerate(G):
        r = n + k
        D = desc(r)
        for pos in range(1, len(g)):
            for f in range(n + len(G)):
                if f in D or f == g[pos]: continue
                G2 = [list(x) for x in G]; G2[k][pos] = f
                tried += 1
                try:
                    vals, _ = evalc(G2)
                except ValueError:
                    continue
                if all((v == w).all() for v, w in zip(vals, want)):
                    correct += 1
                    live = set(); st = list(outs)
                    while st:
                        x = st.pop()
                        if x < n or x in live: continue
                        live.add(x); st += G2[x - n][1:]
                    dead = [n + j for j in range(len(G2)) if n + j not in live]
                    if dead:
                        found.append((r, G[k], pos, g[pos], '->', f, 'dead', dead, 'N rewired' if g[pos] == Nw else ''))
    print(path.split('/')[-1], 'edges x candidates tried', tried, 'correct rewires', correct, 'correct rewires killing a gate', len(found))
    for x in found[:12]: print('  ', x)

for p in sys.argv[1:]: run(p)
