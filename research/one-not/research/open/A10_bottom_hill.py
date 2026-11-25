"""Seat A13: hill-climb for a BOTTOM PAY failure (A10_light_absorption.md).  Run from the repo root:
   python3 -I research/one-not/research/open/A10_bottom_hill.py [--iters N] [--seed s] [--starts K] [--maxn 9] [--time SEC] [--nstates 40]
Score of a correct one-NOT circuit = min over sampled mixed states with a DD set of  slack = |E'| - sum_w need_w,
E' = OR gates outside the top family, 0 at 1_Q, 1 at two atoms P_u,P_u' (u != u') of some DD set (necessary count).
FAILURE = slack < 0, or the exact matroid-union search (`rado` of A10_light_attack, forest form) finds no disjoint payment.
Mutations as A7_hill.py; a mutant is kept when its min slack does not rise.  States are fixed per start circuit family:
all mixed states if n <= 6, else root, singletons and --nstates random states (re-sampled with a fixed seed)."""
import sys, random, time, collections
sys.path.insert(0, 'research/one-not/research/open')
import A7_dd_absorb_attack as A7
import A10_light_attack as A10
from A7_hill import mutate

def state_list(n, seed, k):
    return list(A7.states(n, random.Random(seed), -1 if n <= 6 else k))

def eval_state(c, W, X, FULL, Q, D, stat):
    """returns (slack, rado_ok) or None when the state has no DD set."""
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
    if not any(x[4] for x in alive): return None
    top = set(); rs = []; need = 0; ddsets = []
    for (w, R2, zw, P, dd) in alive:
        if not dd:
            top |= set(A10.uf_run(G, W, n, zw, P)); continue
        U = [u for u in R2 if a >> P[u] & 1]; T = [u for u in R2 if not a >> P[u] & 1]
        if len(U) >= 2: top |= set(A10.uf_run(G, W, n, zw, {u: P[u] for u in U}))
        nd = len(T) - (0 if U else 1)
        cl = {u: (U[0] if u in U else u) for u in R2}
        rs.append((cl, P, nd)); need += nd; ddsets.append(R2)
    E = []
    for k in range(len(G)):
        if k in top or G[k][0] != 'or': continue
        t = W[n + k]
        if t >> qpt & 1: continue
        if any(sum(1 for u in R2 if t >> (qpt | 1 << u) & 1) >= 2 for R2 in ddsets): E.append(k)
    slack = len(E) - need
    ok = True
    if slack < 0: ok = False
    elif slack <= 1:
        stat['rado_calls'] += 1
        ok = A10.rado([W[n + k] for k in E], rs)
    return slack, ok

def score(c, states, stat):
    W, X, FULL = A7.tables(c['n'], c['gates'])
    if not A7.correct(c, W, X): return None
    best = (10**6, None, True)
    for Q, D in states:
        r = eval_state(c, W, X, FULL, Q, D, stat)
        stat['states'] += 1
        if r is None: continue
        stat['dd_states'] += 1
        if r[0] < best[0] or not r[1]: best = (r[0], (sorted(Q), sorted(D)), r[1])
        if not r[1]: break
    return best if best[1] is not None else None

if __name__ == '__main__':
    Ar = sys.argv
    g = lambda f, d: type(d)(Ar[Ar.index(f) + 1]) if f in Ar else d
    iters, seed, starts, maxn, tl, ns = g('--iters', 150), g('--seed', 1), g('--starts', 30), g('--maxn', 9), g('--time', 1100), g('--nstates', 40)
    rng = random.Random(seed); t0 = time.time()
    pool = [c for c in A7.collect(maxn) if c['n'] <= maxn] + [A7.gen_switch(rng, rng.randint(6, maxn)) for _ in range(60)]
    stat = collections.Counter(); steps = 0; glob = (10**6, None); fail = None
    print('pool', len(pool), flush=True)
    for c0 in rng.sample(pool, min(len(pool), starts)):
        if time.time() - t0 > tl: break
        sts = state_list(c0['n'], seed, ns)
        s = score(c0, sts, stat)
        if s is None: continue
        c, cur = c0, s; start = s[0]
        for it in range(iters):
            if time.time() - t0 > tl: break
            d = mutate(c, rng)
            if d is None: continue
            steps += 1
            t = score(d, state_list(d['n'], seed, ns), stat)
            if t is None: continue
            stat['correct_mutants'] += 1
            if t[0] <= cur[0]: c, cur = d, t
            if not cur[2]: fail = (c, cur); break
        if cur[0] < glob[0]: glob = (cur[0], c0['name'])
        print(c0['name'][-40:], 'n', c['n'], 'start min slack', start, 'end', cur[:2], flush=True)
        if fail: print('FAIL', fail); break
    print('SUMMARY seed', seed, 'steps', steps, dict(stat), 'min slack reached', glob, 'failure', bool(fail), 'sec', int(time.time() - t0))
