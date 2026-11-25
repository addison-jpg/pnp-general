"""Seat A10: attack on LIGHT ABSORPTION (board open-one-not), A7's obstacle first.  Run from the repo root:
   python3 -I research/one-not/research/open/A10_light_attack.py [--maxn 9] [--states -1] [--gen K] [--seed 1] [--nostored] [--rado]
Uses A7_dd_absorb_attack (tables, collect, gen_switch, states).  At each mixed state (Q, D) with a DD set:
  top family  = M_v (unit form at Z_v, non-DD v)  u  H_w (unit form at Z_w over heavy atoms U_w, DD w)  (as in A7)
  light run   = unit form at the bottom 1_Q over the light atoms T_w (A7 section 3); light_overlap counts states where
                two DD sets' light runs share a gate (A7's 284 states, the known dead end).
  line run    = L_w: union-find at Z_w over the LINE atoms Z_w + e_u, u in S_w - D (all of them), gates in order.
                G_w = L_w - H_w.  Candidate payment for w: |G_w| >= |T_w| - [U_w empty] (paper, A10 section 2).
  Counts (expected 0 where the paper proves it): G_not_F2, G_not_or, G_short; and the open part:
  G_top (G_w meets the top family), G_GG (G_w meets G_w' for DD w != w'), with the states printed.
  bottom run  = B_w: unit form at 1_Q over S_w - D with the heavy atoms U_w pre-joined (A10 section 1, F2 with witness 1_Q).
                B_short, B_not_or, B_not_F2 expected 0 (paper); B_top, B_BB = states where B_w meets top / another B_w'.
  rado        = is there, inside E = F2Mix - top, for each DD w a set of need_w gates g (g(1_Q) = 0) with one chosen
                pair of w-classes per gate, both atoms 1 under g, forming a forest; rado_fail counts states with none
                (A10 section 3; the exact remaining statement)."""
import sys, collections, random, itertools
sys.path.insert(0, 'research/one-not/research/open')
import A7_dd_absorb_attack as A7

def uf_run_pre(G, W, n, zero, atoms, pre):
    """uf_run with the atoms in `pre` joined before the first gate (the heavy class)."""
    lab = {u: u for u in atoms}
    def find(u):
        while lab[u] != u: u = lab[u]
        return u
    for u in list(pre)[1:]: lab[find(u)] = find(pre[0])
    merged = []
    for k in range(len(G)):
        t = W[n + k]
        if t >> zero & 1: continue
        roots = {find(u) for u in atoms if t >> atoms[u] & 1}
        if len(roots) > 1:
            rs = list(roots)
            for r in rs[1:]: lab[r] = rs[0]
            merged.append(k)
    return merged

def uf_run(G, W, n, zero, atoms, order=None):
    """union-find of the unit/line form: gates 0 at `zero`, joining classes of the atoms (dict u -> point)."""
    lab = {u: u for u in atoms}
    def find(u):
        while lab[u] != u: u = lab[u]
        return u
    merged = []
    for k in range(len(G)):
        t = W[n + k]
        if t >> zero & 1: continue
        roots = {find(u) for u in atoms if t >> atoms[u] & 1}
        if len(roots) > 1:
            rs = list(roots)
            for r in rs[1:]: lab[r] = rs[0]
            merged.append(k)
    return merged

def rado(E, sets):
    """sets: list of (classes: dict atom->class, P: dict atom->point, need).  Gates E: list of truth tables.
    Backtracking: disjoint gate choices, each joining two current classes of its set, need_w joins for set w."""
    sets = sorted(sets, key=lambda s: -s[2])
    A = [[frozenset(cl[u] for u in cl if t >> P[u] & 1) for t in E] for (cl, P, _) in sets]
    def go(i, used, lab, got, start):
        if i == len(sets): return True
        if got == sets[i][2]:
            return go(i + 1, used, None, 0, 0)
        if lab is None: lab = {c: c for c in set(sets[i][0].values())}
        def find(c):
            while lab[c] != c: c = lab[c]
            return c
        for j in range(start, len(E)):
            if used >> j & 1: continue
            roots = sorted({find(c) for c in A[i][j]})
            if len(roots) < 2: continue
            for x, y in itertools.combinations(roots, 2):
                lab2 = dict(lab); lab2[y] = x
                if go(i, used | 1 << j, lab2, got + 1, j + 1): return True
        return False
    return go(0, 0, None, 0, 0)

def f2_witness(G, W, X, FULL, n, Q, D, R2, k):
    box = FULL
    for v in Q: box &= X[v]
    for v in D: box &= FULL ^ X[v]
    for u in R2: box &= FULL ^ X[u]
    t = W[n + k]; m = box & (FULL ^ t)
    one = two = 0
    for u in R2:
        s = (t >> (1 << u)) & m
        two |= one & s; one |= s
    return bool(two)

def check(c, W, X, FULL, Q, D, out):
    n, G, S = c['n'], c['gates'], c['sets']
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]
    qpt = sum(1 << v for v in Q); ALL = (1 << n) - 1
    alive = []
    for w, R in enumerate(S):
        if set(R) & Q: continue
        R2 = [u for u in R if u not in D]
        if len(R2) < 2: continue
        zw = ALL
        for u in R2 + list(D): zw &= ~(1 << u)
        P = {u: qpt | 1 << u for u in R2}
        dd = bool(a >> zw & 1) and any(not (a >> P[u] & 1) for u in R2)
        alive.append((w, R2, zw, P, dd))
    if not any(x[4] for x in alive): return
    out['dd_states'] += 1
    top = collections.Counter(); light = {}; Gw = {}; Bw = {}; rs = []
    for (w, R2, zw, P, dd) in alive:
        if not dd:
            for k in uf_run(G, W, n, zw, P): top[k] += 1
            continue
        U = [u for u in R2 if a >> P[u] & 1]; T = [u for u in R2 if not a >> P[u] & 1]
        H = uf_run(G, W, n, zw, {u: P[u] for u in U}) if len(U) >= 2 else []
        for k in H: top[k] += 1
        light[w] = set(uf_run(G, W, n, qpt, {u: P[u] for u in T})) if len(T) >= 2 else set()
        cl = {u: (U[0] if u in U else u) for u in R2}
        Bm = uf_run_pre(G, W, n, qpt, {u: P[u] for u in R2}, U)
        needB = len(T) - (0 if U else 1)
        out['B_short'] += len(Bm) < needB
        out['B_not_or'] += sum(G[k][0] != 'or' for k in Bm)
        out['B_not_F2'] += sum(not f2_witness(G, W, X, FULL, n, Q, D, R2, k) for k in Bm)
        Bw[w] = set(Bm); rs.append((cl, P, needB))
        L = uf_run(G, W, n, zw, {u: zw | 1 << u for u in R2})
        g = set(L) - set(H)
        need = len(T) - (0 if U else 1)
        out['G_short'] += len(g) < need
        out['G_not_or'] += sum(G[k][0] != 'or' for k in g)
        out['G_not_F2'] += sum(not f2_witness(G, W, X, FULL, n, Q, D, R2, k) for k in g)
        Gw[w] = (g, need)
    ws = list(light)
    wb = list(Bw)
    out['B_top_states'] += any(Bw[x] & set(top) for x in wb)
    out['B_BB_states'] += any(Bw[x] & Bw[y] for i, x in enumerate(wb) for y in wb[i + 1:])
    if RADO:
        F2 = [k for k in range(len(G)) if k not in top and G[k][0] == 'or' and not W[n + k] >> qpt & 1
              and any(f2_witness(G, W, X, FULL, n, Q, D, R2, k) for (_, R2, _, _, _) in alive)]
        ok = rado([W[n + k] for k in F2], rs)
        out['rado_ok'] += ok; out['rado_fail'] += not ok
        if not ok and len(out.setdefault('rado_ex', [])) < 4: out['rado_ex'].append((c.get('name'), sorted(Q), sorted(D)))
    lo = any(light[x] & light[y] for i, x in enumerate(ws) for y in ws[i + 1:])
    out['light_overlap_states'] += lo
    bad_top = any(g & set(top) for g, _ in Gw.values())
    bad_GG = any(Gw[x][0] & Gw[y][0] for i, x in enumerate(ws) for y in ws[i + 1:])
    out['G_top_states'] += bad_top; out['G_GG_states'] += bad_GG
    if lo: out['G_top_at_light_overlap'] += bad_top; out['G_GG_at_light_overlap'] += bad_GG
    # does the injective count survive anyway?  |union G_w - top| >= sum need (necessary for this payment to close)
    union = set().union(*[g for g, _ in Gw.values()]) - set(top)
    out['G_union_short'] += len(union) < sum(nd for _, nd in Gw.values())
    if (bad_top or bad_GG) and len(out.setdefault('ex', [])) < 6:
        out['ex'].append((c.get('name'), sorted(Q), sorted(D), {w: (sorted(g), nd) for w, (g, nd) in Gw.items()}, sorted(set(top))))

if __name__ == '__main__':
    A = sys.argv
    maxn = int(A[A.index('--maxn') + 1]) if '--maxn' in A else 9
    k = int(A[A.index('--states') + 1]) if '--states' in A else -1
    rng = random.Random(int(A[A.index('--seed') + 1]) if '--seed' in A else 1)
    cs = [] if '--nostored' in A else A7.collect(maxn)
    if '--gen' in A: cs += [A7.gen_switch(rng) for _ in range(int(A[A.index('--gen') + 1]))]
    RADO = '--rado' in A
    out = collections.Counter()
    for c in cs:
        W, X, FULL = A7.tables(c['n'], c['gates'])
        if not A7.correct(c, W, X): continue
        out['circuits'] += 1
        for Q, D in A7.states(c['n'], rng, k): check(c, W, X, FULL, Q, D, out)
    ex = out.pop('ex', []) + out.pop('rado_ex', [])
    print(dict(out))
    for e in ex: print(e)
