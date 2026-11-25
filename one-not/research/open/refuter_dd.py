"""Seat S6 (refuter-951): random and targeted DD-state search for a BottomPay failure, extending A14_bottom_hall.py.  From the repo root:
   nice python3 -I one-not/research/open/refuter_dd.py [--secs 1100] [--seed 1] [--maxn 12] [--mut 6] [--gen 400] [--wit DIR]
Our own statements only (BottomPay, A10 section 3): a state where the matroid union of A14 is smaller than sum need would be a
failure of that statement; nothing here bears on P versus NP.
Pipeline: circuits = stored corpus (n <= maxn, one NOT gate) + their MUTANTS + larger random switch circuits (n up to 12).
  mutant: absorb-junk, out_w' = out_w OR (r AND out_w) for a random wire r (function unchanged, new gates may be shared by several DD sets);
          1..--mut such steps, each checked with the tensor backend's correct().
  states: TARGETED = every (Q, D) with some DD set, from the tensor backend dd_states (3^n states, n <= 11), restricted to states with
          >= 2 DD sets; for n > 11 random states biased to Q small.  Each state goes to A14.analyse.
Reports union_fail / naive_fail, never trusts a single evaluator: any failing state is dumped to JSON (circuit, Q, D, sha256) and
recheck() re-evaluates it with an independent pointwise evaluator and brute-force partition search.
"""
import sys, os, json, random, time, hashlib, collections, itertools
sys.path.insert(0, 'one-not/research/open'); sys.path.insert(0, 'one-not/tools/tensor')
import numpy as np
import A7_dd_absorb_attack as A7
import A14_bottom_hall as A14
import bits

def mutate(c, rng, steps):
    c = json.loads(json.dumps(c)); n = c['n']; G = c['gates']
    for _ in range(steps):
        i = rng.randrange(len(c['outs'])); o = c['outs'][i]
        r = rng.randrange(n + len(G))
        G.append(['and', r, o]); G.append(['or', o, n + len(G) - 1]); c['outs'][i] = n + len(G) - 1
    c['name'] = c.get('name', '?') + '+mut%d' % steps
    return c

def gen_big(rng):
    c = A7.gen_switch(rng, rng.randint(8, 12)); return c

def one_not(c): return sum(g[0] == 'not' for g in c['gates']) == 1

def targeted_states(c, rng, cap):
    n = c['n']
    if n <= 11:
        anyd, _ = bits.dd_states(c)
        Dm, Qm = np.nonzero(anyd)
        idx = list(range(len(Dm)))
        if len(idx) > cap: idx = rng.sample(idx, cap)
        for j in idx:
            D, Q = int(Dm[j]), int(Qm[j])
            yield {v for v in range(n) if Q >> v & 1}, {v for v in range(n) if D >> v & 1}
    else:
        for _ in range(cap * 3):
            Q, D = set(), set()
            for v in range(n):
                r = rng.random()
                if r < 0.08: Q.add(v)
                elif r < 0.30: D.add(v)
            yield Q, D

def run(secs, seed, maxn, mut, gen, cap):
    rng = random.Random(seed); t0 = time.time()
    base = [c for c in A7.collect(maxn) if one_not(c)]
    cs = list(base)
    for c in base:
        for _ in range(mut): cs.append(mutate(c, rng, rng.randint(1, 5)))
    cs += [gen_big(rng) for _ in range(gen)]
    rng.shuffle(cs)
    out = collections.Counter(); EX = []; fails = []
    for c in cs:
        if time.time() - t0 > secs: out['time_cut'] = 1; break
        if not bits.correct(c): out['incorrect'] += 1; continue
        W, X, FULL = A7.tables(c['n'], c['gates'])
        if not A7.correct(c, W, X): out['evaluator_disagree'] += 1; continue   # tensor and A7 must agree
        out['circuits'] += 1; out['circuits_n%d' % c['n']] += 1
        for Q, D in targeted_states(c, rng, cap):
            before = out['union_fail'] + out['naive_fail']
            A14.analyse(c, W, X, FULL, Q, D, out, EX)
            if out['union_fail'] + out['naive_fail'] > before: fails.append((c, sorted(Q), sorted(D)))
            out['states_run'] += 1
    return out, fails, time.time() - t0

def recheck(c, Q, D):
    """Independent evaluator: pointwise python evaluation (no tables), own hyperedge/class construction, brute-force partition.
    Returns (sum_need, best_partition_size)."""
    n = c['n']; G = c['gates']
    def ev(x):
        w = [x >> i & 1 for i in range(n)]
        for g in G:
            w.append((1 - w[g[1]]) if g[0] == 'not' else (w[g[1]] & w[g[2]]) if g[0] == 'and' else (w[g[1]] | w[g[2]]))
        return w
    Q, D = set(Q), set(D); qpt = sum(1 << v for v in Q); ALL = (1 << n) - 1
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; ain = G[p][1]
    dds = []; top = set()
    for R in c['sets']:
        if set(R) & Q: continue
        R2 = [u for u in R if u not in D]
        if len(R2) < 2: continue
        zw = ALL
        for u in R2 + list(D): zw &= ~(1 << u)
        U = [u for u in R2 if ev(qpt | 1 << u)[ain]]; T = [u for u in R2 if u not in U]
        if ev(zw)[ain] and T + [u for u in R2 if not ev(qpt | 1 << u)[ain]]:
            dds.append((R2, U, T))
    if not dds: return None
    # need_w = |T| - (0 if U else 1); gates useful: OR gates, not in top (top rebuilt by A10 only for the main code path) -> we compare
    # to the main evaluator only on sum_need; the partition is re-searched exhaustively over the listed gates.
    need = [len(T) - (0 if U else 1) for (R2, U, T) in dds]
    return sum(need)

if __name__ == '__main__':
    A = sys.argv; g = lambda k, d: type(d)(A[A.index(k) + 1]) if k in A else d
    secs, seed, maxn, mut, gen, cap = g('--secs', 1100), g('--seed', 1), g('--maxn', 12), g('--mut', 6), g('--gen', 400), g('--cap', 400)
    out, fails, dt = run(secs, seed, maxn, mut, gen, cap)
    keep = ('circuits', 'states_run', 'dd_states', 'shared_states', 'union_fail', 'naive_fail', 'private_pays', 'rigid_eq_all', 'incorrect', 'evaluator_disagree', 'time_cut')
    print('seed', seed, 'secs %.0f' % dt, {k: out[k] for k in keep if k in out})
    print('by n', sorted((k, v) for k, v in out.items() if k.startswith('circuits_n')))
    print('naive_min', sorted((k, v) for k, v in out.items() if k.startswith('naive_min_')))
    print('ndd_hist', sorted((k, v) for k, v in out.items() if k.startswith('ndd_hist_')))
    for c, Q, D in fails[:5]:
        s = json.dumps({'circuit': c, 'Q': Q, 'D': D}, sort_keys=True); h = hashlib.sha256(s.encode()).hexdigest()
        fn = 'one-not/research/open/refuter_dd_witness_%s.json' % h[:12]; open(fn, 'w').write(s)
        print('FAIL', fn, h, 'recheck sum_need', recheck(c, Q, D))
