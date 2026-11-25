"""Outward search: mutate correct circuits, keep correctness, push the margin of one conjecture down.
A margin below 0 is a counterexample; it is saved under found/. Hill climbing with restarts: finding nothing proves nothing.
Run from the repo root:
  python3 -I one-not/tools/search/hunt.py "<conjecture name>" SECONDS MAX_NOT [seed] [start.json ...]
Serves README items C2, C3, C4."""
import sys, os, json, time, random, glob, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
from conjectures import REGISTRY

def or_tree(n, sets):
    G = []; outs = []
    for R in sets:
        cur = R[0]
        for u in R[1:]:
            G.append(['or', cur, u]); cur = n + len(G) - 1
        outs.append(cur)
    return {"n": n, "sets": sets, "gates": G, "outs": outs}

def mutate(c, rng, max_not):
    c = copy.deepcopy(c); n, G = c['n'], c['gates']; m = rng.random()
    if m < 0.35 and G:                                   # rewire one input of a gate to an earlier wire
        k = rng.randrange(len(G)); g = G[k]; j = rng.randrange(1, len(g)); g[j] = rng.randrange(n + k)
    elif m < 0.75:                                       # insert a new gate and feed it into a later gate
        k = rng.randrange(len(G) + 1); ops = ['and', 'or'] + (['not'] if nots(c) < max_not else [])
        op = rng.choice(ops); a = rng.randrange(n + k); b = rng.randrange(n + k)
        new = [op, a] if op == 'not' else [op, a, b]
        G.insert(k, new); sh = lambda x: x + 1 if x >= n + k else x
        for i, g in enumerate(G):
            if i > k: g[1:] = [sh(x) for x in g[1:]]
        c['outs'] = [sh(o) for o in c['outs']]
        later = [i for i in range(k + 1, len(G))]
        if later:
            i = rng.choice(later); g = G[i]
            if g[0] != 'not' and rng.random() < 0.7:     # splice: input x becomes (x OR new) or (x AND new)
                j = rng.randrange(1, 3); x = g[j]
                G.insert(i, [rng.choice(['and', 'or']), x, n + k]); sh2 = lambda y: y + 1 if y >= n + i else y
                for t, h in enumerate(G):
                    if t > i: h[1:] = [sh2(y) for y in h[1:]]
                c['outs'] = [sh2(o) for o in c['outs']]
                G[i + 1][j] = n + i
            else: g[rng.randrange(1, len(g))] = n + k
    elif m < 0.9 and G:                                  # flip AND / OR
        k = rng.randrange(len(G))
        if G[k][0] != 'not': G[k][0] = 'and' if G[k][0] == 'or' else 'or'
    else:                                                # move an output to another wire
        i = rng.randrange(len(c['outs'])); c['outs'][i] = n + rng.randrange(len(G)) if G else c['outs'][i]
    return c

def splice(c, k, block, final):
    """Insert `block` before gate k and replace gate k by `final`. In block and final, a wire -1 - i means block gate i.
    Gate k keeps its wire, so every reader of it is unchanged."""
    n, G = c['n'], c['gates']; L = len(block)
    loc = lambda x: n + k + (-1 - x) if x < 0 else x
    sh = lambda x: x + L if x >= n + k else x
    newblock = [[g[0]] + [loc(x) for x in g[1:]] for g in block]
    for i in range(k, len(G)): G[i][1:] = [sh(x) for x in G[i][1:]]
    G[k] = [final[0]] + [loc(x) if x < 0 else x for x in final[1:]]
    G[k:k] = newblock
    c['outs'] = [sh(o) for o in c['outs']]
    return c

def rewrite(c, rng, max_not):
    """Equivalence-preserving local rewrites: the function of every wire is unchanged, so correctness is kept."""
    c = copy.deepcopy(c); n, G = c['n'], c['gates']
    cand = [k for k, g in enumerate(G) if g[0] != 'not']
    if not cand: return c
    k = rng.choice(cand); op, a, b = G[k]; free = max_not - nots(c); m = rng.random()
    j = rng.randrange(n + k)
    if m < 0.25 and free >= 3:      # De Morgan
        dual = 'and' if op == 'or' else 'or'
        return splice(c, k, [['not', a], ['not', b], [dual, -1, -2]], ['not', -3])
    if m < 0.5 and free >= 1:       # a = (a AND j) OR (a AND NOT j)
        return splice(c, k, [['not', j], ['and', a, j], ['and', a, -1], ['or', -2, -3]], [op, -4, b])
    if m < 0.75:                    # a = a OR (a AND j)
        return splice(c, k, [['and', a, j], ['or', a, -1]], [op, -2, b])
    return splice(c, k, [['or', a, j], ['and', a, -1]], [op, -2, b])   # a = a AND (a OR j)

def main():
    name, secs, max_not = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0; rng = random.Random(seed); f = REGISTRY[name]
    starts = []
    for p in sys.argv[5:] or sorted(glob.glob('one-not/data/witnesses/*.json')):
        d = json.load(open(p, encoding="utf-8"))
        if d['n'] <= 8: starts.append({"n": d['n'], "sets": d['sets'], "gates": [list(g) for g in d['gates']], "outs": d['outs']})
    starts += [or_tree(c['n'], c['sets']) for c in starts]
    t0 = time.time(); tried = kept = 0; best_all = None; found = 0
    os.makedirs('one-not/tools/search/found', exist_ok=True)
    while time.time() - t0 < secs:
        cur = copy.deepcopy(rng.choice(starts)); mc = f(cur)[0]; stall = 0
        while time.time() - t0 < secs and stall < 400:
            new = (rewrite if rng.random() < 0.4 else mutate)(cur, rng, max_not); tried += 1
            if len(new['gates']) > 70 or nots(new) > max_not or not correct(new): stall += 1; continue
            new = prune(new)
            mn = f(new)[0]
            if mn <= mc:
                stall = 0 if mn < mc else stall + 1; cur, mc = new, mn; kept += 1
                if best_all is None or mc < best_all[0]: best_all = (mc, copy.deepcopy(cur))
                if mc < 0:
                    found += 1; p = f"one-not/tools/search/found/{name.split()[0]}_seed{seed}_{found}.json"
                    json.dump(dict(cur, name=f"hunt {name}", margin=mc), open(p, "w", encoding="utf-8", newline="\n")); print("FOUND", p, "margin", mc, "gates", len(cur['gates']), "NOT", nots(cur)); break
            else: stall += 1
    b = best_all
    print(f"{name} | max NOT {max_not} | seed {seed} | {tried} mutations, {kept} kept | counterexamples {found} | least margin {b[0] if b else None}" + (f" (n = {b[1]['n']}, {len(b[1]['gates'])} gates, {nots(b[1])} NOT)" if b else ""))
if __name__ == "__main__": main()
