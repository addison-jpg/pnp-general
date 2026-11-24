# fano_corpus.py (scaffold 951, 2026-11-24): reproducible corpus of CORRECT one-NOT circuits for the Fano plane (base 14).
# 60 seeds: monotone (a|b)|c per line, NOT on x_b, and in 1-3 lines through b the gadget ((x_a & ~x_b) | x_b) | x_c.
# Random walk (seed 1 and 2, 150000 steps, s <= 40, restart every 400): rewire a slot / insert a random gate / a -> (a&N)|(a&h)
# / bypass a gate; prune dangling; accept iff correct with exactly one (used) NOT. Every distinct accepted circuit is written.
#   python3 fano_corpus.py OUT.jsonl          (expected: 80,198 distinct incl. FANO-FORMULA + 60 seeds; ~2 min)
# Landed by coord (scaffold cannot push; owner: keep the corpus). sha256 of the sorted keys json.dumps([gates, outs]),
# per scaffold: 64ca2c153627554eb20161b3b97cfff3ea3e24d9ca249509b0e34e473737923d
import sys, json, random
from functools import reduce
LINES = [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]

def tables(c, force=None):
    n, G = c['n'], c['gates']; R = 1 << n; full = (1 << R) - 1
    T = [sum(((r >> i) & 1) << r for r in range(R)) for i in range(n)]
    for g in G:
        a = T[g[1]]
        if g[0] == 'not': T.append(full & ~a if force is None else (0 if force == 0 else full))
        else: T.append(a & T[g[2]] if g[0] == 'and' else a | T[g[2]])
    return T

def correct(c):
    T = tables(c)
    return all(T[o] == reduce(lambda a, b: a | b, [T[u] for u in S]) for S, o in zip(c['sets'], c['outs']))

def essential(c):
    T = tables(c); T0 = tables(c, 0); T1 = tables(c, 1)
    return any(T0[o] != T[o] for o in c['outs']) and any(T1[o] != T[o] for o in c['outs'])

def insert(c, pos, gate):
    n = c['n']; sh = lambda x: x + 1 if x >= n + pos else x
    G = [[g[0]] + [sh(a) for a in g[1:]] for g in c['gates']]
    G.insert(pos, gate)
    return {'n': n, 'sets': c['sets'], 'gates': G, 'outs': [sh(o) for o in c['outs']]}

def delete_dangling(c):
    n = c['n']; used = set(c['outs'])
    for k in range(len(c['gates']) - 1, -1, -1):
        if n + k in used:
            for a in c['gates'][k][1:]: used.add(a)
    keep = [k for k in range(len(c['gates'])) if n + k in used]
    if len(keep) == len(c['gates']): return c
    mp = {n + k: n + i for i, k in enumerate(keep)}; f = lambda x: x if x < n else mp[x]
    return {'n': n, 'sets': c['sets'], 'gates': [[c['gates'][k][0]] + [f(a) for a in c['gates'][k][1:]] for k in keep], 'outs': [f(o) for o in c['outs']]}

def mutate(c, rng):
    n = c['n']; s = len(c['gates']); p = [k for k, g in enumerate(c['gates']) if g[0] == 'not'][0]
    op = rng.random()
    k = rng.randrange(s)
    if c['gates'][k][0] == 'not': return None
    slot = rng.choice([1, 2])
    if op < 0.4:
        G = [list(g) for g in c['gates']]; G[k][slot] = rng.randrange(n + k)
        return delete_dangling({'n': n, 'sets': c['sets'], 'gates': G, 'outs': list(c['outs'])})
    if op < 0.75:
        a, b = rng.randrange(n + k), rng.randrange(n + k)
        c2 = insert(c, k, [rng.choice(['and', 'or']), a, b])
        G = c2['gates']; G[k + 1][slot] = n + k
        return delete_dangling(c2)
    a = c['gates'][k][slot]; hw = c['gates'][p][1]; N = n + p
    if N >= n + k or hw >= n + k: return None
    c2 = insert(c, k, ['and', a, N]); c2 = insert(c2, k + 1, ['and', a, hw]); c2 = insert(c2, k + 2, ['or', n + k, n + k + 1])
    c2['gates'][k + 3][slot] = n + k + 2
    return c2

def bypass(c, rng):
    n = c['n']; s = len(c['gates']); k = rng.randrange(s); g = c['gates'][k]
    if g[0] == 'not': return None
    ch = rng.choice(g[1:]); wk = n + k
    G = [[x[0]] + [ch if a == wk else a for a in x[1:]] for x in c['gates']]
    outs = [ch if o == wk else o for o in c['outs']]
    return delete_dangling({'n': n, 'sets': c['sets'], 'gates': G, 'outs': outs})

def fano_formula():
    last = [0, 3, 5, 1, 4, 6, 2]; n = 7; G = [['and', 0, 1], ['and', 7, 2], ['not', 8]]; outs = []
    for S, l in zip(LINES, last):
        a, b = [u for u in S if u != l]; G.append(['or', a, b]); G.append(['or', n + len(G) - 1, l]); outs.append(n + len(G) - 1)
    return {'n': 7, 'sets': LINES, 'gates': G, 'outs': outs}

def seeds():
    rng = random.Random(11); out = []
    for trial in range(60):
        n = 7; G = []
        def add(*g): G.append(list(g)); return n + len(G) - 1
        b = rng.randrange(7); N = add('not', b); outs = []
        gl = [L for L in LINES if b in L]; chosen = rng.sample(gl, rng.choice([1, 2, 3]))
        for L in LINES:
            if L in chosen:
                a = rng.choice([u for u in L if u != b]); cc = [u for u in L if u not in (a, b)][0]
                t = add('and', a, N); t = add('or', t, b); t = add('or', t, cc); outs.append(t)
            else:
                q = L[:]; rng.shuffle(q); t = add('or', q[0], q[1]); t = add('or', t, q[2]); outs.append(t)
        out.append({'n': 7, 'sets': LINES, 'gates': G, 'outs': outs})
    return out

def walk(sd, rseed, steps=150000, smax=40, restart=400):
    rng = random.Random(rseed); seen = set(); cur = None; res = []
    for t in range(steps):
        if cur is None or t % restart == 0:
            d = rng.choice(sd); cur = {k: d[k] for k in ('n', 'sets', 'gates', 'outs')}
        c2 = bypass(cur, rng) if rng.random() < 0.25 else mutate(cur, rng)
        if c2 is None or len(c2['gates']) > smax: continue
        if sum(g[0] == 'not' for g in c2['gates']) != 1 or not correct(c2): continue
        cur = c2; key = json.dumps([c2['gates'], c2['outs']], separators=(',', ':'))
        if key in seen: continue
        seen.add(key); res.append(('rw:%d:%d' % (rseed, t), c2))
    return res

if __name__ == '__main__':
    out = open(sys.argv[1], 'w'); allc = [('FANO-FORMULA', fano_formula())]; sd = seeds()
    allc += [('seed%d' % i, c) for i, c in enumerate(sd)]
    for r in (1, 2): allc += walk(sd, r)
    seen = set(); k = 0
    for src, c in allc:
        key = json.dumps([c['gates'], c['outs']])
        if key in seen: continue
        seen.add(key); k += 1
        out.write(json.dumps({'src': src, 'ess': essential(c), **c}, separators=(',', ':')) + '\n')
    print(k, 'circuits')
