"""Experiments for task beyond-one-not (README items C4, T6). Run from the repo root, one at a time:
  python3 -I research/one-not/tools/beyond_one_not/experiments.py local   SECONDS SEED         per-set flip-classes lemma (a theorem; this is a test of the code)
  python3 -I research/one-not/tools/beyond_one_not/experiments.py notfree SECONDS MAXNOT SEED  hunt: #AND/OR gates (NOT gates free) >= base
  python3 -I research/one-not/tools/beyond_one_not/experiments.py worlds  SECONDS T SEED       the 2^t worlds: faces, live NOT patterns, circuits with no correct face
Hill climbing and random walks: finding nothing proves nothing."""
import sys, os, json, time, random, glob, copy, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'search'))
from core import *
import conjectures, hunt

def load_corpus(nmax=8):
    out = []
    for p in sorted(glob.glob('research/one-not/data/witnesses/*.json') + glob.glob('research/one-not/data/witnesses/nonlocal/*.json')):
        try: d = json.load(open(p))
        except Exception: continue
        if not isinstance(d, dict) or 'gates' not in d or d['n'] > nmax: continue
        c = {"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']}
        if correct(c): out.append((p, c))
    return out

SMALL = [(5, [[0, 1, 2], [0, 3, 4]]), (6, [[0, 1, 2], [2, 3, 4], [4, 5, 0]]), (7, [[0, 1, 2, 3], [0, 4, 5, 6]]),
         (7, [[0, 1, 2], [0, 3, 4], [0, 5, 6]]), (6, [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]),
         (7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]])]

def local_min(c):
    """min over sets R and zero points Z of R of (#classes of wires, up to complement, that change at >= 2 atoms of R from Z) - (|R| - 1)."""
    n = c['n']; w = tables(n, c['gates']); M = (1 << (1 << n)) - 1; worst = None
    for R in c['sets']:
        for Z in conjectures._zeros(n, tuple(R), 0):
            cl = set()
            for k in range(len(c['gates'])):
                t = w[n + k]; b = t >> Z & 1
                if sum((t >> (Z | 1 << u) & 1) != b for u in R) >= 2: cl.add(min(t, M ^ t))
            m = len(cl) - (len(R) - 1)
            if worst is None or m < worst: worst = m
    return worst

def walk(starts, secs, max_not, rng, maxg=40):
    """Random walk over correct circuits (mutations and rewrites of hunt.py), pruned."""
    t0 = time.time()
    while time.time() - t0 < secs:
        cur = copy.deepcopy(rng.choice(starts))
        for _ in range(300):
            if time.time() - t0 >= secs: break
            new = (hunt.rewrite if rng.random() < 0.5 else hunt.mutate)(cur, rng, max_not)
            if len(new['gates']) > maxg or nots(new) > max_not or not correct(new): continue
            cur = prune(new); yield cur

def cmd_local(secs, seed):
    rng = random.Random(seed); corp = load_corpus(8); bad = 0; least = None
    for p, c in corp:
        m = local_min(c); least = m if least is None else min(least, m); bad += m < 0
    print(f"local lemma | corpus: {len(corp)} correct circuits with n <= 8 | failures {bad} | least margin {least}")
    starts = [c for _, c in corp if c['n'] <= 7] + [hunt.or_tree(n, s) for n, s in SMALL]
    seen = 0; bad = 0; least = None; byt = {}
    for c in walk(starts, secs, 6, rng):
        m = local_min(c); seen += 1; bad += m < 0; least = m if least is None else min(least, m)
        t = nots(c); byt[t] = byt.get(t, 0) + 1
        if m < 0: json.dump(c, open(f'research/one-not/data/beyond_one_not/local_fail_{seen}.json', 'w')); print("FAIL", c)
    print(f"local lemma | random walk seed {seed}, {secs:.0f} s, <= 6 NOT gates: {seen} correct circuits | failures {bad} | least margin {least} | by number of NOT gates {dict(sorted(byt.items()))}")

def cmd_notfree(secs, max_not, seed):
    conjectures.REGISTRY["notfree: binary gates >= base"] = lambda c: (len(c['gates']) - nots(c) - base(c), "AND/OR gates - base")
    hunt.REGISTRY = conjectures.REGISTRY
    sys.argv = ['hunt.py', "notfree: binary gates >= base", str(secs), str(max_not), str(seed)]
    hunt.main()

def face_tables(n, G, pat):
    N = 1 << n; M = (1 << N) - 1; w = tables(n, []); i = 0
    for g in G:
        if g[0] == 'not': w.append(M if pat >> i & 1 else 0); i += 1
        else: w.append(w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]])
    return w

def worlds(c):
    """(t, number of faces that are correct on ALL inputs, number of NOT-output patterns that occur at some input)."""
    n, G = c['n'], c['gates']; t = nots(c); good = 0
    for pat in range(1 << t):
        good += correct(c, face_tables(n, G, pat))
    w = tables(n, G); nk = [n + k for k, g in enumerate(G) if g[0] == 'not']
    live = {tuple(w[k] >> x & 1 for k in nk) for x in range(1 << n)}
    return t, good, len(live)

def dups(c):
    """Number of wires that are constant or repeat the function of an earlier wire (0 = the normal form of enum_small.c; NOT of NOT gives 1)."""
    w = tables(c['n'], c['gates']); M = (1 << (1 << c['n'])) - 1; seen = set(); d = 0
    for t in w:
        if t in seen or t == 0 or t == M: d += 1
        seen.add(t)
    return d

def cmd_worlds(secs, T, seed):
    rng = random.Random(seed); corp = load_corpus(8)
    if T == 0:
        print("file | NOT gates | faces correct everywhere / 2^t | live NOT patterns | gates - base | repeated functions")
        for p, c in corp:
            if 1 <= nots(c) <= 6:
                t, good, live = worlds(c); print(f"  {os.path.basename(p)} | {t} | {good} / {1 << t} | {live} | {len(c['gates']) - base(c)} | {dups(c)}")
        return
    irr = []
    p = 'research/one-not/tools/search/found/irreducible_seed7.jsonl'
    if os.path.exists(p):
        for line in open(p):
            d = json.loads(line); d = d.get('circuit', d)
            if d['n'] <= 8: irr.append({"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']})
    starts = irr + [c for _, c in corp if c['n'] <= 7] + [hunt.or_tree(n, s) for n, s in SMALL[:5]]
    # hill climbing: among correct circuits with exactly T NOT gates, first push (correct faces + repeated functions) to 0, then the gate count down
    def score(c):
        if nots(c) != T: return (1 << 10, len(c['gates']))
        return (worlds(c)[1] + dups(c), len(c['gates']))
    t0 = time.time(); tried = 0; stats = {}; best = None; livemax = 0
    while time.time() - t0 < secs:
        cur = copy.deepcopy(rng.choice(starts)); sc = score(cur); stall = 0
        while time.time() - t0 < secs and stall < 300:
            new = (hunt.rewrite if rng.random() < 0.4 else hunt.mutate)(cur, rng, T); tried += 1
            if len(new['gates']) > 40 or nots(new) > T or not correct(new): stall += 1; continue
            new = prune(new); sn = score(new)
            if nots(new) == T:
                key = 'no face correct, no repeated function' if sn[0] == 0 else 'other'; stats[key] = stats.get(key, 0) + 1
            if sn <= sc:
                stall = 0 if sn < sc else stall + 1; cur, sc = new, sn
                if sn[0] == 0:
                    sav = len(cur['gates']) - base(cur); livemax = max(livemax, worlds(cur)[2])
                    if best is None or sav < best[0]: best = (sav, copy.deepcopy(cur))
            else: stall += 1
    print(f"worlds | exactly {T} NOT gates | seed {seed} | {secs:.0f} s | {tried} mutations | circuits met with exactly {T} NOT gates: {stats}")
    if best:
        c = best[1]; path = f'research/one-not/data/beyond_one_not/essential_t{T}_seed{seed}.json'
        json.dump(dict(c, name=f"no face correct, no repeated function, {T} NOT gates", gates_minus_base=best[0]), open(path, 'w'))
        print(f"  least (gates - base) among circuits with NO correct face and no repeated function: {best[0]} (n = {c['n']}, {len(c['gates'])} gates, base {base(c)}, all gates read: {all_read(c)}); most live NOT patterns seen {livemax} of {1 << T}; saved {path}")
    else: print("  no circuit with exactly T NOT gates, no correct face and no repeated function was met")

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == 'local': cmd_local(float(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'notfree': cmd_notfree(float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif cmd == 'worlds': cmd_worlds(float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
