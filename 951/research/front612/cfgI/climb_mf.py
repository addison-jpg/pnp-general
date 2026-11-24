"""Hill-climb from Config (I) toward a MergeFrac contradiction (full LP L* > 1 = a refutation of MergeFrac).
Moves: rewire one gate input to a random earlier wire, flip and/or, or append a redundant gate and reroute a reader through it.
Keep: correct (every output = OR of its set), exactly one NOT. Score: (L*_MF, #world assignments with L > 1).
Usage: python3 climb_mf.py SEED SECONDS OUT.jsonl"""
import itertools, json, random, sys, time
sys.path.insert(0, '/home/user/c951/tools')
from w951 import Circuit, load
import cfgI_prices as P

def score(c):
    Z = [P.zero_menu(c, w) for w in range(len(c.sets))]
    L, _ = P.solve_items([[t[2] for t in zm] for zm in Z])
    bad = 0
    for a in itertools.product((0, 1), repeat=len(Z)):
        menus = [[t[2] for t in zm if t[1] == a[w]] for w, zm in enumerate(Z)]
        if all(menus) and P.solve_items(menus)[0] > 1 + 1e-9: bad += 1
    return L, bad

def mutate(d, rng):
    d = json.loads(json.dumps(d)); n = d['n']; G = d['gates']
    k = rng.randrange(len(G)); g = G[k]; w = n + k
    r = rng.random()
    if r < 0.5 and g[0] != 'not':
        i = rng.choice([1, 2]); g[i] = rng.randrange(w)
    elif r < 0.7 and g[0] != 'not':
        g[0] = 'and' if g[0] == 'or' else 'or'
    else:
        a, b = rng.randrange(w), rng.randrange(w)
        G.insert(k, [rng.choice(['and', 'or']), a, b])
        sh = lambda x: x + 1 if x >= n + k else x
        for j in range(k + 1, len(G)):
            G[j] = [G[j][0]] + [sh(x) for x in G[j][1:]]
        d['outs'] = [sh(o) for o in d['outs']]
        j = rng.randrange(k + 1, len(G))
        if G[j][0] != 'not': G[j][rng.choice([1, 2])] = n + k
    return d

seed, secs, out = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
rng = random.Random(seed); cur = load('cfgI.json')[0].to_dict(); cs = score(Circuit.from_dict(cur)); best = cs
t0 = time.time(); it = acc = 0; fo = open(out, 'a', buffering=1)
while time.time() - t0 < secs:
    it += 1
    d = mutate(cur, rng)
    try:
        c = Circuit.from_dict(d)
        if len(c.nots) != 1 or c.s > 40 or not c.is_correct(): continue
        s = score(c)
    except Exception:
        continue
    if s >= cs or rng.random() < 0.02:
        cur, cs = d, s; acc += 1
        if s > best:
            best = s; fo.write(json.dumps({'L': s[0], 'bad_worlds': s[1], 's': c.s, 'c': d}) + '\n')
            print(f'{time.time()-t0:7.0f}s it={it} NEW BEST L*={s[0]:.6f} bad_worlds={s[1]} s={c.s}', flush=True)
            if s[0] > 1 + 1e-9: print('!!! MergeFrac CONTRADICTION FOUND', flush=True)
print(f'done it={it} accepted={acc} best={best}')
