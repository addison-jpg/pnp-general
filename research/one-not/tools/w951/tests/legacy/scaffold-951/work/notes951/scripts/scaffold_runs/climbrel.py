# Adversarial hill-climb against FracMatch / the mix rule: mutate correct essential one-NOT circuits (insert a gate on
# two earlier wires and reroute one reader of a wire to it, or retarget an input) keeping outputs correct, C0 and C1
# wrong, NOT in an output cone; accept moves that do not lower the score (L*, then mix). Any L* > 1 or mix > 1 is printed.
#   python3 climb.py SEEDS.jsonl STEPS SEED MAXSIZE OUT.log
import sys, os, json, random, time
args = sys.argv[1:]; sys.argv = ['x']
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import contextlib, io
with contextlib.redirect_stdout(io.StringIO()):
    import relrule as RR, nsets
seeds = [json.loads(l) for l in open(args[0])]; STEPS = int(args[1]); rng = random.Random(int(args[2])); MAXS = int(args[3])
def ev(n, G, x, cv=None):
    w = [(x >> i) & 1 for i in range(n)]
    for g in G:
        if g[0] == 'not': w.append((1 - w[g[1]]) if cv is None else cv)
        elif g[0] == 'and': w.append(w[g[1]] & w[g[2]])
        else: w.append(w[g[1]] | w[g[2]])
    return w
def ok(c):
    n, G, S, O = c['n'], c['gates'], c['sets'], c['outs']
    want = lambda x, s_: int(any(x >> v & 1 for v in s_))
    for x in range(1 << n):
        w = ev(n, G, x)
        if any(w[o] != want(x, s_) for s_, o in zip(S, O)): return False
    wrong = lambda cv: any(ev(n, G, x, cv)[o] != want(x, s_) for x in range(1 << n) for s_, o in zip(S, O))
    if not (wrong(0) and wrong(1)): return False
    p = [k for k, g in enumerate(G) if g[0] == 'not'][0]; cone = set(); st = list(O)
    while st:
        i = st.pop()
        if i < n or i in cone: continue
        cone.add(i); st += G[i - n][1:]
    return n + p in cone
def score(c):
    """Tractability's relative-sandwich rule (relrule.run, WT=2): L_rel (LP; rule works iff <= 1), then the number of
    gates that appear in items of >= 2 different sets (cross-set collisions, which the rule was never climbed against)."""
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            L, _, F = RR.run(c, '', 2, False, False)
    except Exception: return None
    if L == float('inf'): L = 99.0
    owners = {}
    for w, m in enumerate(F):
        for C, z in m:
            for g in C: owners.setdefault(g, set()).add(w)
    cross = sum(1 for g, ws in owners.items() if len(ws) >= 2)
    return (L, cross)
def mutate(c):
    n, G, O = c['n'], [list(g) for g in c['gates']], list(c['outs']); s = len(G)
    r = rng.random()
    if r < 0.6 and s < MAXS:          # insert gate at position k, reroute one later reader input to it
        k = rng.randint(0, s); W = n + k
        a, b = rng.randrange(W), rng.randrange(W)
        if a == b: return None
        newg = [rng.choice(['and', 'or']), a, b]
        G2 = []
        for i, g in enumerate(G):
            if i == k: G2.append(newg)
            G2.append([g[0]] + [x + 1 if x >= W else x for x in g[1:]])
        if k == s: G2.append(newg)
        O2 = [o + 1 if o >= W else o for o in O]
        readers = [(i, j) for i in range(k + 1, len(G2)) for j in range(1, len(G2[i])) if G2[i][0] != 'not']
        if readers:
            i, j = rng.choice(readers); G2[i][j] = W
        return {'n': n, 'sets': c['sets'], 'gates': G2, 'outs': O2}
    else:                              # retarget one input of a gate to another earlier wire
        i = rng.randrange(s)
        if G[i][0] == 'not': return None
        j = rng.randint(1, 2); G[i][j] = rng.randrange(n + i)
        if rng.random() < 0.3: G[i][0] = 'and' if G[i][0] == 'or' else 'or'
        return {'n': n, 'sets': c['sets'], 'gates': G, 'outs': O}
log = open(args[4], 'a', buffering=1); best_all = (0, 0); t0 = time.time()
for si, c in enumerate(seeds):
    cur = c; sc = score(cur)
    if sc is None or not ok(cur): continue
    for step in range(STEPS):
        m = mutate(cur)
        if m is None or not ok(m): continue
        s2 = score(m)
        if s2 is None: continue
        if s2[0] > 1 + 1e-9:
            cls = nsets.analyse(json.loads(json.dumps(m)))[0]
            print('RELFAIL L_rel=%.4f cross=%d nsets=%s' % (s2[0], s2[1], cls), json.dumps(m), flush=True)
            log.write('FAIL ' + json.dumps({'L_rel': s2[0], 'cross': s2[1], 'nsets': cls, 'c': m}) + '\n')
        if s2 >= sc: cur, sc = m, s2
        if sc > best_all: best_all = sc
    log.write(json.dumps({'seed': si, 'final': sc, 'size': len(cur['gates'])}) + '\n')
print('done', len(seeds), 'seeds; best (L*, mix) =', best_all, f'{time.time()-t0:.0f}s', flush=True)
