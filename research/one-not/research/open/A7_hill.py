"""Seat A7: hill-climb toward a DD-absorption failure.  python3 -I research/one-not/research/open/A7_hill.py [--iters N] [--seed s]
Start from stored one-NOT circuits (n <= 8) and switch circuits; mutate gate inputs/ops; keep a correct one-NOT circuit
if its minimum DD-absorption slack (over ALL mixed states) does not rise.  Prints any state with slack < 0."""
import sys, random, itertools, collections
sys.path.insert(0, 'research/one-not/research/open')
import A7_dd_absorb_attack as A

def allstates(n):
    for code in itertools.product(range(3), repeat=n):
        yield {v for v in range(n) if code[v] == 1}, {v for v in range(n) if code[v] == 2}

def score(c):
    W, X, FULL = A.tables(c['n'], c['gates'])
    if not A.correct(c, W, X): return None
    out = collections.Counter(); best = (99, None)
    for Q, D in allstates(c['n']):
        sl = A.check_state(c, W, X, FULL, Q, D, out)
        if sl is not None and sl < best[0]: best = (sl, (sorted(Q), sorted(D)))
    return best

def mutate(c, rng):
    n = c['n']; G = [list(g) for g in c['gates']]; k = rng.randrange(len(G)); g = G[k]
    r = rng.random()
    if g[0] == 'not':
        g[1] = rng.randrange(n + k)
    elif r < 0.6:
        g[rng.choice([1, 2])] = rng.randrange(n + k)
    elif r < 0.8:
        g[0] = 'and' if g[0] == 'or' else 'or'
    else:
        g[1], g[2] = rng.randrange(n + k), rng.randrange(n + k)
    d = dict(c); d['gates'] = G
    if sum(x[0] == 'not' for x in G) != 1: return None
    # NOT input must not depend on the NOT gate (it never does: inputs are earlier wires, one NOT)
    return d

if __name__ == '__main__':
    Ar = sys.argv
    iters = int(Ar[Ar.index('--iters') + 1]) if '--iters' in Ar else 300
    rng = random.Random(int(Ar[Ar.index('--seed') + 1]) if '--seed' in Ar else 7)
    pool = [c for c in A.collect(8) if c['n'] <= 8] + [A.gen_switch(rng, rng.randint(6, 8)) for _ in range(20)]
    glob_best = 99
    for c0 in rng.sample(pool, min(len(pool), 40)):
        s = score(c0)
        if s is None or s[1] is None: continue
        c, cur = c0, s
        for it in range(iters):
            d = mutate(c, rng)
            if d is None: continue
            t = score(d)
            if t is None or t[1] is None: continue
            if t[0] <= cur[0]: c, cur = d, t
            if cur[0] < 0: break
        glob_best = min(glob_best, cur[0])
        print(c0['name'][-40:], 'n', c['n'], 'min absorption slack', cur, flush=True)
        if cur[0] < 0:
            print('FAIL', c); break
    print('global min', glob_best)
