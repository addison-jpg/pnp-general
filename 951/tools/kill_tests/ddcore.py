"""DD core (cTAHG, 2026-11-24): per output C_0/C_1 vs s, DD-normality, N-dependent live gates (cones, C_0-/C_1-equality),
U-game on the lifted outputs.  python3 -I 951/tools/kill_tests/ddcore.py FILE.json ..."""
import sys, json
import numpy as np
sys.path.insert(0, 'tools/kill_tests')
import ugame

def analyse(path):
    d = json.load(open(path)); n = d['n']; S = d['sets']; G = d['gates']; outs = d['outs']; P = 1 << n
    idx = np.arange(P, dtype=np.int64)
    def ev(nv):
        W = [((idx >> i) & 1).astype(bool) for i in range(n)]
        for g in G:
            if g[0] == 'not': W.append(~W[g[1]] if nv is None else np.full(P, bool(nv)))
            elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
            else: W.append(W[g[1]] | W[g[2]])
        return W
    W = ev(None); W0 = ev(0); W1 = ev(1)
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; Nw = n + p; h = W[G[p][1]]
    # liveness and cones
    def cone(o):
        seen = set(); st = [o]
        while st:
            x = st.pop()
            if x < n or x in seen: continue
            seen.add(x); st += G[x - n][1:]
        return seen
    cones = [cone(o) for o in outs]
    live = set().union(*cones)
    print(path.split('/')[-1], 'n', n, 's', len(G), 'live', len(live), 'base', sum(len(R) - 1 for R in S), 'h support',
          [u for u in range(n) if (h != h[idx ^ (1 << u)]).any()], 'heavy', [u for u in range(n) if h[1 << u]])
    for w, (o, R) in enumerate(zip(outs, S)):
        s = np.zeros(P, bool)
        for u in R: s |= W[u]
        dd0 = (W0[o] == (s & h)).all(); dd1 = (W1[o] == (s | h)).all()
        print('  set', w, R, 'C0==s', (W0[o] == s).all(), 'C1==s', (W1[o] == s).all(), 'DD-normal: C0=s&h', dd0, 'C1=s|h', dd1,
              'N in cone', Nw in cones[w])
    # N-dependent live gates (C0 != C1), private / shared N-cone
    ndep = [i for i in sorted(live) if not (W0[i] == W1[i]).all()]
    print('  N-dependent live gates', len(ndep), ':', ndep)
    for i in ndep:
        ins = [w for w in range(len(outs)) if i in cones[w]]
        eq0 = (W[i] == W0[i]).all(); eq1 = (W[i] == W1[i]).all()
        print('    gate', i, G[i - n], 'in cones of', ins, 'real==C0', eq0, 'real==C1', eq1)
    # U-game on lifted outputs
    N = n + 1; PP = 1 << N; I2 = np.arange(PP, dtype=np.int64)
    L = [((I2 >> i) & 1).astype(bool) for i in range(n)]; y = ((I2 >> n) & 1).astype(bool)
    for g in G:
        if g[0] == 'not': L.append(y.copy())
        elif g[0] == 'and': L.append(L[g[1]] & L[g[2]])
        else: L.append(L[g[1]] | L[g[2]])
    O = [L[o].astype(np.int8).tolist() for o in outs]
    print('  U-game', 'WON' if ugame.solve(N, S, O) else 'LOST')

for f in sys.argv[1:]: analyse(f)
