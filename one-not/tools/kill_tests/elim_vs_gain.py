"""What gates < base buys at a cube (cTAHG, coord 13:48 (b)): F2 gain versus gate elimination.

For a one-NOT circuit and a point v (at Q = {} unless --Q is given) this prints
  gain(v)   = |F2(Q) \\ F2(Q+v)|,   cost(v) = sum of d_w over alive w through v,
  s1(v)     = size of the circuit restricted to x_v := 1 after removing constant wires, copies of inputs,
              duplicate functions and dead wires (live = in the cone of an output of an alive set not through v),
  elim1(v)  = s - s1(v),
  s0(v), elim0(v) = the same for x_v := 0 (all sets, with v deleted).
In a minimal counterexample lex-minimality forces s1(v) >= base(Q+v) (the restricted instance is not a smaller
counterexample), so elim1(v) <= s - base(Q+v) < cost(v); and MinCE.heredity forces elim0(v) <= deg(v).
So the F2 STEP gain(v) >= cost(v) can hold in a MinCE only through F2 gates that leave F2 WITHOUT being eliminated.
python3 -I one-not/tools/kill_tests/elim_vs_gain.py FILE.json [--Q bitmask]
python3 -I one-not/tools/kill_tests/elim_vs_gain.py --corpus FILE_OR_DIR ...   one json line per correct one-NOT circuit at Q = {}:
    GE (some v with elim1(v) >= cost(v), the elimination step of ElimStep.lean `no_minCE_of_elimStep`), step (F2 step),
    best = max_v (elim1 - cost), surv = rows with F2 losers surviving the restriction.
  surv(v)   = number of F2 gates leaving F2 under x_v := 1 that survive the restriction (kept in s1(v)).
  gain(v) <= surv(v) + elim1(v), so in a MinCE the STEP at v needs surv(v) >= cost(v) - elim1(v) > 0.
"""
import sys, json
import numpy as np


def tables(d):
    n = d['n']; G = d['gates']; P = 1 << n; idx = np.arange(P, dtype=np.int64)
    W = [((idx >> i) & 1).astype(bool) for i in range(n)]
    for g in G:
        if g[0] == 'not':
            W.append(~W[g[1]])
        elif g[0] == 'and':
            W.append(W[g[1]] & W[g[2]])
        else:
            W.append(W[g[1]] | W[g[2]])
    return W


def f2_tables(d, W):
    n = d['n']; S = d['sets']; G = d['gates']; P = 1 << n; idx = np.arange(P, dtype=np.int64)
    up = lambda T, a: T[idx | (1 << a)]
    A = {}
    for k, g in enumerate(G):
        if g[0] != 'or':
            continue
        i = n + k
        m = np.zeros(P, bool)
        for R in S:
            av = np.ones(P, bool)
            for u in R:
                av &= ~W[u]
            cnt = sum(up(W[i], u).astype(np.int8) for u in R)
            m |= ~W[i] & av & (cnt >= 2)
        for v in range(n):
            m = m | up(m, v)   # m[Q]: some witness zero point Z >= Q
        A[i] = m
    return A


def simplified_size(d, W, sel, live_outs):
    """number of distinct, non-constant, non-input, live gate functions on the points sel"""
    n = d['n']; G = d['gates']
    rep = {}
    keyof = {}
    for i in range(n):
        keyof[i] = W[i][sel].tobytes()
    seen = {keyof[i]: i for i in range(n)}
    const = {np.zeros(sel.sum(), bool).tobytes(), np.ones(sel.sum(), bool).tobytes()}
    keep = []
    for k in range(len(G)):
        i = n + k
        key = W[i][sel].tobytes()
        if key in const or key in seen:
            rep[i] = seen.get(key)
            continue
        seen[key] = i
        rep[i] = i
        keep.append(i)
    # liveness: cones of the live outputs, through representatives
    keyset = {i: W[i][sel].tobytes() for i in range(n + len(G))}
    first = {}
    for i in range(n + len(G)):
        first.setdefault(keyset[i], i)
    live = set()
    st = [first[keyset[o]] for o in live_outs]
    while st:
        x = st.pop()
        if x < n or x in live:
            continue
        live.add(x)
        for j in G[x - n][1:]:
            st.append(first[keyset[j]])
    return [i for i in keep if i in live]


def main(path, Q=0, verbose=True, d=None):
    d = d if d is not None else json.load(open(path))
    n = d['n']; S = d['sets']; outs = d['outs']; P = 1 << n; idx = np.arange(P, dtype=np.int64)
    W = tables(d)
    A = f2_tables(d, W)
    s = len(d['gates'])
    onQ = (idx & Q) == Q
    alive = [i for i, R in enumerate(S) if not any(Q >> u & 1 for u in R)]
    base = sum(len(S[i]) - 1 for i in alive)
    F2Q = [i for i in A if A[i][Q]]
    rows = []
    if verbose:
      print('file', path, 'n', n, 's', s, 'Q', Q, 'base(Q)', base, '|F2(Q)|', len(F2Q), 'size slack s-base(Q)', s - base)
      print(' v  deg cost gain  s1 base1 elim1 surv | s0 elim0 | need')
    for v in range(n):
        if Q >> v & 1:
            continue
        star = [i for i in alive if v in S[i]]
        if not star:
            continue
        cost = sum(len(S[i]) - 1 for i in star)
        gain = sum(1 for i in F2Q if not A[i][Q | 1 << v])
        sel1 = onQ & ((idx >> v) & 1).astype(bool)
        rest = [i for i in alive if v not in S[i]]
        K1 = simplified_size(d, W, sel1, [outs[i] for i in rest])
        s1 = len(K1)
        surv = sum(1 for i in F2Q if not A[i][Q | 1 << v] and i in K1)
        base1 = sum(len(S[i]) - 1 for i in rest)
        sel0 = onQ & ~((idx >> v) & 1).astype(bool)
        s0 = len(simplified_size(d, W, sel0, [outs[i] for i in alive]))
        rows.append(dict(v=v, deg=len(star), cost=cost, gain=gain, s1=s1, base1=base1, elim1=s - s1, surv=surv, s0=s0,
                         elim0=s - s0))
        if verbose:
            print('%2d %4d %4d %4d %4d %5d %5d %4d | %3d %5d | %d' % (v, len(star), cost, gain, s1, base1, s - s1, surv, s0,
                                                                     s - s0, max(0, cost - (s - s1))))
    return dict(s=s, base=base, F2=len(F2Q), rows=rows)


def corpus(paths):
    import os
    seen = set()
    for p in paths:
        files = []
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                files += [os.path.join(root, f) for f in sorted(fs) if f.endswith(('.json', '.jsonl'))]
        else:
            files = [p]
        for f in files:
            lines = open(f).read().splitlines() if f.endswith('.jsonl') else [open(f).read()]
            for i, l in enumerate(lines):
                try:
                    d = json.loads(l)
                    d = dict(n=d['n'], sets=d['sets'], gates=d['gates'], outs=d['outs'])
                except Exception:  # noqa: BLE001
                    continue
                key = json.dumps(d)
                if key in seen or sum(g[0] == 'not' for g in d['gates']) != 1:
                    continue
                seen.add(key)
                try:
                    W = tables(d)
                    ok = all((W[o] == np.logical_or.reduce([W[u] for u in R])).all() for o, R in zip(d['outs'], d['sets']))
                except Exception:  # noqa: BLE001
                    continue
                if not ok:
                    continue
                r = main(f, 0, verbose=False, d=d)
                rows = r['rows']
                print(json.dumps(dict(name='%s:%d' % (f, i), n=d['n'], s=r['s'], base=r['base'], F2=r['F2'],
                                      GE=any(x['elim1'] >= x['cost'] for x in rows),
                                      step=any(x['gain'] >= x['cost'] for x in rows),
                                      best=max((x['elim1'] - x['cost'] for x in rows), default=None),
                                      surv=sum(1 for x in rows if x['surv'] > 0))), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == '--corpus':
        corpus(sys.argv[2:])
        sys.exit(0)
    Q = 0
    if '--Q' in sys.argv:
        Q = int(sys.argv[sys.argv.index('--Q') + 1])
    main(sys.argv[1], Q)
