"""Seat A7: attack on DD-absorption (board open-one-not) on stored one-NOT circuits with n up to 16, sampled states.
   python3 -I one-not/research/open/A7_dd_absorb_attack.py [--maxn 16] [--states 300] [--seed 1] [--gen K] [--nostored]   (--states -1: every mixed state)
Truth tables are Python ints over the 2^n points.  At a state (Q, D) (disjoint):
  P_u = 1_Q + e_u, Z_w = 1 off S_w u D, h = the NOT gate's input.
  DD(w): w alive (S_w cap Q empty), |S_w - D| >= 2, h(Z_w) = 1, h(P_t) = 0 for some t in S_w - D.
  M_w (non-DD w): the merges of the unit-form union-find (zero point Z_w, atoms P_u, gates in order).
  F2Mix: OR gates with a witness Z (Z = 1 on Q, 0 on S_w u D, gate 0 at Z and 1 at Z+e_u, Z+e_u', u != u' in S_w - D) for an alive w.
  DD-absorption: |F2Mix - U_{non-DD} M_w| >= sum_{DD w} (|S_w - D| - 1).  Prints failures (expected 0) and tight counts.
  Top family: M_w (non-DD) and H_w (DD: unit form at Z_w over the HEAVY atoms, h(P_u) = 1); top_overlap, top_not_F2,
  top_merge_not_or count violations of the paper lemmas (expected 0).  Light absorption (residual):
  |F2Mix - top family| >= sum_{DD w} (|T_w| - [no heavy atom]), T_w = light atoms (h(P_t) = 0); light_fail counts failures.
--gen K adds K random NOT-switch circuits from gen_switch (many DD sets by construction)."""
import sys, json, glob, itertools, collections, random

def tables(n, G):
    N = 1 << n; FULL = (1 << N) - 1
    X = []
    for v in range(n):
        t = 0
        for p in range(N):
            if p >> v & 1: t |= 1 << p
        X.append(t)
    W = list(X)
    for g in G:
        if g[0] == 'not': W.append(FULL ^ W[g[1]])
        elif g[0] == 'and': W.append(W[g[1]] & W[g[2]])
        elif g[0] == 'or': W.append(W[g[1]] | W[g[2]])
        elif g[0] == 'const': W.append(FULL if g[1] else 0)
        else: raise ValueError(g)
    return W, X, FULL

def correct(c, W, X):
    for R, o in zip(c['sets'], c['outs']):
        f = 0
        for u in R: f |= X[u]
        if W[o] != f: return False
    return True

def check_state(c, W, X, FULL, Q, D, out):
    n, G, S = c['n'], c['gates'], c['sets']
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; a = W[G[p][1]]
    qpt = sum(1 << v for v in Q)
    box0 = FULL
    for v in Q: box0 &= X[v]
    for v in D: box0 &= FULL ^ X[v]
    alive = []
    for w, R in enumerate(S):
        if set(R) & Q: continue
        R2 = [u for u in R if u not in D]
        if len(R2) < 2: continue
        zw = (1 << n) - 1
        for u in R2: zw &= ~(1 << u)
        for u in D: zw &= ~(1 << u)
        P = {u: qpt | 1 << u for u in R2}
        dd = bool(a >> zw & 1) and any(not (a >> P[u] & 1) for u in R2)
        alive.append((w, R2, zw, P, dd))
    bdd = sum(len(R2) - 1 for (_, R2, _, _, dd) in alive if dd)
    if not bdd: return None
    nd = set(); top = set(); light_need = 0
    for (w, R2, zw, P, dd) in alive:
        if dd:
            U = [u for u in R2 if a >> P[u] & 1]; T = [u for u in R2 if not a >> P[u] & 1]
            light_need += len(T) - (0 if U else 1)
            R2 = U  # heavy merges H_w: unit form at Z_w over the heavy atoms only
            if len(R2) < 2: continue
        lab = {u: u for u in R2}
        def find(u):
            while lab[u] != u: u = lab[u]
            return u
        for k in range(len(G)):
            t = W[n + k]
            if t >> zw & 1: continue
            roots = {find(u) for u in R2 if t >> P[u] & 1}
            if len(roots) > 1:
                rs = list(roots)
                for r in rs[1:]: lab[r] = rs[0]
                if G[k][0] != 'or': out['top_merge_not_or'] += 1
                if k in top: out['top_overlap'] += 1
                top.add(k)
                if not dd: nd.add(k)
    F2 = set()
    for (w, R2, zw, P, dd) in alive:
        box = box0
        for u in R2: box &= FULL ^ X[u]
        for k, g in enumerate(G):
            if g[0] != 'or' or k in F2: continue
            t = W[n + k]; m = box & (FULL ^ t)
            if not m: continue
            one = two = 0
            for u in R2:
                s = (t >> (1 << u)) & m
                two |= one & s; one |= s
            if two: F2.add(k)
    sl = len(F2 - nd) - bdd
    out['top_not_F2'] += len(top - F2)
    slR = len(F2 - top) - light_need          # residual: light absorption
    out['light_fail'] += slR < 0; out['light_tight'] += slR == 0
    if slR < 0 and len(out.get('light_ex', [])) < 3: out.setdefault('light_ex', []).append((c.get('name'), sorted(Q), sorted(D), slR))
    out['dd_states'] += 1; out['dd_sets'] += sum(dd for *_, dd in alive)
    out['max_dd_sets'] = max(out['max_dd_sets'], sum(dd for *_, dd in alive))
    out['tight'] += sl == 0
    if sl < 0:
        out['FAIL'] += 1
        out.setdefault('fail_ex', []).append((c.get('name'), sorted(Q), sorted(D), sl)) if len(out.get('fail_ex', [])) < 5 else None
    # full mixed count too
    msl = len(F2) - sum(len(R2) - 1 for (_, R2, *_ ) in alive)
    out['mixed_neg'] += msl < 0
    return sl

def states(n, rng, k):
    if k < 0:  # every mixed state
        for code in itertools.product(range(3), repeat=n):
            yield {v for v in range(n) if code[v] == 1}, {v for v in range(n) if code[v] == 2}
        return
    yield set(), set()
    for v in range(n):
        yield {v}, set(); yield set(), {v}
    for _ in range(k):
        Q, D = set(), set()
        for v in range(n):
            r = rng.random()
            if r < 0.15: Q.add(v)
            elif r < 0.35: D.add(v)
        yield Q, D

def collect(maxn):
    seen = {}
    def add(name, d):
        if not (isinstance(d, dict) and all(k in d for k in ('n', 'sets', 'gates', 'outs'))): return
        if d['n'] > maxn or sum(g[0] == 'not' for g in d['gates']) != 1: return
        if any(len(set(x) & set(y)) > 1 for x, y in itertools.combinations(d['sets'], 2)): return
        c = {'n': d['n'], 'sets': [list(s) for s in d['sets']], 'gates': [list(g) for g in d['gates']], 'outs': list(d['outs']), 'name': name}
        seen.setdefault(json.dumps([c['n'], c['sets'], c['gates'], c['outs']]), c)
    for f in glob.glob('one-not/data/**/*.json', recursive=True):
        try: d = json.load(open(f, encoding='utf-8'))
        except Exception: continue
        for i, x in enumerate(d if isinstance(d, list) else [d]):
            add('%s:%d' % (f, i), x.get('circuit', x) if isinstance(x, dict) else x)
    for f in glob.glob('one-not/**/*.jsonl', recursive=True):
        if 'findings' in f: continue
        for i, line in enumerate(open(f, encoding='utf-8')):
            try: d = json.loads(line)
            except Exception: continue
            if isinstance(d, dict): d = d.get('c', d.get('circuit', d))
            add('%s:%d' % (f, i), d)
    return list(seen.values())

def gen_switch(rng, n=None):
    """Random NOT-switch circuit: h = random monotone (OR of ANDs of 2-3 inputs), g = NOT h;
    out_w = X_w OR (g AND Y_w) with X_w = OR of a random subset T of S_w OR (h AND OR(S_w - T)) built as
    X_w = OR(T) OR (h AND OR(S_w-T)), Y_w = OR(S_w - T).  Correct for every h; DD whenever h(Z_w)=1, h(e_t)=0."""
    n = n or rng.randint(6, 11)
    # set system: random pairwise <=1-intersecting sets of size 2..4
    sets = []
    for _ in range(rng.randint(2, 7)):
        k = rng.randint(2, 4); R = sorted(rng.sample(range(n), k))
        if all(len(set(R) & set(x)) <= 1 for x in sets): sets.append(R)
    G = []
    def gate(op, *a):
        G.append([op] + list(a)); return n + len(G) - 1
    def OR(items):
        items = list(items); rng.shuffle(items)
        while len(items) > 1:
            x = items.pop(); y = items.pop(); items.insert(rng.randint(0, len(items)), gate('or', x, y))
        return items[0]
    terms = [gate('and', *rng.sample(range(n), 2)) for _ in range(rng.randint(1, 4))]
    h = OR(terms); g = gate('not', h)
    outs = []
    for R in sets:
        T = [u for u in R if rng.random() < 0.5]; U = [u for u in R if u not in T]
        if not U: outs.append(OR(R)); continue
        y = OR(U); parts = list(T) + [gate('and', h, y), gate('and', g, y)]
        outs.append(OR(parts))
    return {'n': n, 'sets': sets, 'gates': G, 'outs': outs, 'name': 'switch'}

if __name__ == '__main__':
    A = sys.argv
    maxn = int(A[A.index('--maxn') + 1]) if '--maxn' in A else 16
    k = int(A[A.index('--states') + 1]) if '--states' in A else 300
    rng = random.Random(int(A[A.index('--seed') + 1]) if '--seed' in A else 1)
    cs = [] if '--nostored' in A else collect(maxn)
    if '--gen' in A: cs += [gen_switch(rng) for _ in range(int(A[A.index('--gen') + 1]))]
    out = collections.Counter(); byn = collections.Counter()
    for c in cs:
        W, X, FULL = tables(c['n'], c['gates'])
        if not correct(c, W, X): out['incorrect_skipped'] += 1; continue
        out['circuits'] += 1; byn[c['n']] += 1
        for Q, D in states(c['n'], rng, k): check_state(c, W, X, FULL, Q, D, out)
    print('by n', sorted(byn.items())); print(dict(out))
