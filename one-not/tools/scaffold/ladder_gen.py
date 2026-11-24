import sys, json, glob, random, time, itertools, os
F15='/tmp/claude-0/-home-user/dbc7162d-d362-5361-8133-bb93548aca7c/scratchpad/f15'
sys.path.insert(0, F15); sys.path.insert(0, F15 + '/heavy'); os.chdir(F15)
import ladder as LD

_inp = {}
def inputs(n):
    if n in _inp: return _inp[n]
    R = 1 << n; full = (1 << R) - 1; T = []
    for i in range(n):
        p = 1 << (i + 1); blk = ((1 << (1 << i)) - 1) << (1 << i)
        T.append(blk * (full // ((1 << p) - 1)))
    _inp[n] = (T, full); return _inp[n]

def evalc(n, G, nval=None):
    T0, full = inputs(n); T = list(T0)
    for g in G:
        if g[0] == 'not':
            T.append(full & ~T[g[1]] if nval is None else (full if nval else 0))
        elif g[0] == 'and': T.append(T[g[1]] & T[g[2]])
        else: T.append(T[g[1]] | T[g[2]])
    return T

def targets(n, sets):
    T0, full = inputs(n); out = []
    for S in sets:
        t = 0
        for u in S: t |= T0[u]
        out.append(t)
    return out

def check(c, tg=None):
    n = c['n']; tg = tg or targets(n, c['sets'])
    T = evalc(n, c['gates'])
    if any(T[o] != t for o, t in zip(c['outs'], tg)): return None
    for v in (0, 1):
        T = evalc(n, c['gates'], v)
        if all(T[o] == t for o, t in zip(c['outs'], tg)): return 'ok'
    return 'ess'

def prune(c):
    n = c['n']; G = c['gates']; live = set(c['outs'])
    for k in range(len(G) - 1, -1, -1):
        if n + k in live:
            for a in G[k][1:]: live.add(a)
    mp = {i: i for i in range(n)}; NG = []
    for k, g in enumerate(G):
        if n + k in live:
            mp[n + k] = n + len(NG); NG.append([g[0]] + [mp[a] for a in g[1:]])
    return {'n': n, 'sets': c['sets'], 'gates': NG, 'outs': [mp[o] for o in c['outs']]}

def key(c): return json.dumps([c['gates'], c['outs']])
def slack(c): return len(c['gates']) - sum(len(S) - 1 for S in c['sets'])

def embed_map(sets, lines, rng, tries=20):
    pts = sorted({u for S in sets for u in S}); N = max(max(l) for l in lines) + 1
    lset = [frozenset(l) for l in lines]
    for _ in range(tries):
        order = pts[:]; rng.shuffle(order); mp = {}; used = set(); cnt = [0]
        def ok_partial():
            for S in sets:
                im = [mp[u] for u in S if u in mp]
                if len(im) >= 2 and not any(set(im) <= l for l in lset): return False
            return True
        def rec(i):
            cnt[0] += 1
            if cnt[0] > 5000: return False
            if i == len(order): return True
            u = order[i]; cand = [p for p in range(N) if p not in used]; rng.shuffle(cand)
            for p in cand:
                mp[u] = p; used.add(p)
                if ok_partial() and rec(i + 1): return True
                del mp[u]; used.discard(p)
            return False
        if not rec(0): continue
        opts = [[j for j, l in enumerate(lset) if {mp[u] for u in S} <= l] for S in sets]
        idx = list(range(len(sets))); rng.shuffle(idx); asg = {}
        def rec2(t, usedl):
            if t == len(idx): return True
            i = idx[t]; o = opts[i][:]; rng.shuffle(o)
            for j in o:
                if j in usedl: continue
                asg[i] = j; usedl.add(j)
                if rec2(t + 1, usedl): return True
                usedl.discard(j)
            return False
        if rec2(0, set()): return mp, asg
    return None

def build(c, mp, asg, N, lines):
    n0 = c['n']; f = lambda w: mp[w] if w < n0 else w - n0 + N
    NG = [[g[0]] + [f(a) for a in g[1:]] for g in c['gates']]
    nxt = N + len(NG); outs = [None] * len(lines); inv = {j: i for i, j in asg.items()}
    for j, L in enumerate(lines):
        if j in inv:
            S = c['sets'][inv[j]]; cur = f(c['outs'][inv[j]]); imS = {mp[u] for u in S}
            rest = [p for p in L if p not in imS]
        else:
            cur = L[0]; rest = L[1:]
        for p in rest:
            NG.append(['or', cur, p]); cur = nxt; nxt += 1
        outs[j] = cur
    return {'n': N, 'sets': [list(L) for L in lines], 'gates': NG, 'outs': outs}

def move(c, rng):
    n = c['n']; G = [list(g) for g in c['gates']]; outs = list(c['outs']); m = len(G)
    r = rng.random()
    if r < 0.4:
        readers = [(k, j) for k, g in enumerate(G) for j in range(1, len(g))] + [(-1 - i, 0) for i in range(len(outs))]
        k, j = rng.choice(readers)
        lim = n + k if k >= 0 else n + m
        a, b = rng.randrange(lim), rng.randrange(lim)
        if a == b: return None
        pos = k if k >= 0 else m
        sh = lambda w: w + 1 if w >= n + pos else w
        NG = [[g[0]] + [sh(x) for x in g[1:]] for g in G]; nouts = [sh(o) for o in outs]
        NG.insert(pos, [rng.choice(['or', 'and']), a, b]); nw = n + pos
        if k >= 0: NG[k + 1][j] = nw
        else: nouts[-1 - k] = nw
        return prune({'n': n, 'sets': c['sets'], 'gates': NG, 'outs': nouts})
    elif r < 0.75:
        k = rng.randrange(m); j = rng.randrange(1, len(G[k]))
        G[k][j] = rng.randrange(n + k)
        return prune({'n': n, 'sets': c['sets'], 'gates': G, 'outs': outs})
    else:
        k = rng.randrange(m)
        if G[k][0] == 'not': return None
        t = rng.choice(G[k][1:]); w = n + k
        for g in G:
            for j in range(1, len(g)):
                if g[j] == w: g[j] = t
        outs = [t if o == w else o for o in outs]
        return prune({'n': n, 'sets': c['sets'], 'gates': G, 'outs': outs})

def load_pool():
    pool = []
    fs = glob.glob('/home/user/pw-data/ess/*clean*') + glob.glob('/home/user/pw-data/ess/bad*') + glob.glob('/home/user/pw-data/q/q_*.jsonl') + glob.glob('/home/user/pw-data/fixh/fixh16_clean.jsonl') + glob.glob('/home/user/pw-data/tri/tri_smoke.jsonl')
    for f in fs:
        for l in open(f):
            try: c = json.loads(l)
            except Exception: continue
            if max(map(len, c['sets'])) <= 4 and c['n'] <= 8: pool.append(c)
    for f in glob.glob(F15 + '/logs/h4/*.log'):
        for l in open(f):
            if '"gates"' in l:
                try: c = json.loads(l)
                except Exception: continue
                for cand in ([c, c.get('circuit')] if isinstance(c, dict) else []):
                    if isinstance(cand, dict) and 'gates' in cand and 'outs' in cand and cand['n'] <= 8: pool.append(cand)
    return pool

def main():
    name, seed, budget = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    rng = random.Random(seed); N, lines = LD.SPACES[name](); tg = targets(N, lines)
    outf = F15 + '/ladder' + '/' + name + '.jsonl'
    seen = set(); found = []; embs = []
    if os.path.exists(outf):
        for l in open(outf):
            d = json.loads(l); seen.add(key(d['circuit'])); found.append(d)
    pool = load_pool(); print('pool', len(pool), flush=True)
    t0 = time.time(); mrng = random.Random(seed + 1)
    def record(c, src):
        m = LD.metrics(c, mrng, kmax=4, nstates=100)
        d = {'circuit': c, 'src': src, 'metrics': m}; found.append(d)
        with open(outf, 'a') as f: f.write(json.dumps(d) + '\n')
        return m
    while time.time() - t0 < budget * 0.35:
        c = rng.choice(pool)
        if slack(c) > 5 or check(c) != 'ess': continue
        r = embed_map(c['sets'], lines, rng)
        if not r: continue
        big = build(c, r[0], r[1], N, lines)
        if slack(big) != slack(c) or check(big, tg) != 'ess': print('EMBED FAIL', slack(big), slack(c)); continue
        k = key(big)
        if k in seen: continue
        seen.add(k); m = record(big, 'embed'); embs.append((big, m))
        print('embed', len(embs), 'slack', m['slack'], 'k*', m['kstar_max'], 'ms', m['MergeSDR'], round(time.time() - t0), flush=True)
    while time.time() - t0 < budget and embs:
        embs.sort(key=lambda e: (-e[1]['kstar_max'], e[1]['slack']))
        cur, cm = rng.choice(embs[:max(3, len(embs) // 3)]) if rng.random() < .7 else rng.choice(embs)
        s0 = cm['slack']; score = (cm['kstar_max'], -cm['slack']); steps = 0; acc = 0
        while time.time() - t0 < budget and steps < 4000 and acc < 25:
            steps += 1
            d = move(cur, rng)
            if d is None or slack(d) > s0 + 3: continue
            k = key(d)
            if k in seen: continue
            if check(d, tg) != 'ess': continue
            seen.add(k); m = record(d, 'climb'); sc = (m['kstar_max'], -m['slack'])
            embs.append((d, m)); acc += 1
            if sc >= score:
                cur, cm, score = d, m, sc
                print('climb acc', len(found), 'slack', m['slack'], 'k*', m['kstar_max'], 'ms', m['MergeSDR'], round(time.time() - t0), flush=True)
    print('done', len(found), round(time.time() - t0))
main()
