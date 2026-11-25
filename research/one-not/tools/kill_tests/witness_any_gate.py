# General witness gates (README D9): the witness condition for ANY gate type and ANY number of NOT gates.
# Test: replace OR gates by their De Morgan form NOT(AND(NOT a, NOT b)) (3 extra NOT gates each).
# The OR-only family loses gates; the any-gate family must still have >= base members if D9 is the right definition.
# Run: python3 -I research/one-not/tools/kill_tests/witness_any_gate.py
import json, glob, os, itertools, random
def tables(n, G):
    N = 1 << n; M = (1 << N) - 1; w = []
    for i in range(n):
        t = 0
        for x in range(N):
            if x >> i & 1: t |= 1 << x
        w.append(t)
    for g in G:
        w.append(M ^ w[g[1]] if g[0] == 'not' else (w[g[1]] & w[g[2]] if g[0] == 'and' else w[g[1]] | w[g[2]]))
    return w
def correct(n, S, G, outs):
    w = tables(n, G)
    for R, o in zip(S, outs):
        t = 0
        for u in R: t |= w[u]
        if w[o] != t: return False
    return True
def witness(n, S, G, only_or):
    w = tables(n, G); out = set()
    for k, g in enumerate(G):
        if only_or and g[0] != 'or': continue
        t = w[n + k]; hit = False
        for R in S:
            rest = [v for v in range(n) if v not in R]
            for r in range(len(rest) + 1):
                for Zs in itertools.combinations(rest, r):
                    Z = sum(1 << v for v in Zs)
                    if t >> Z & 1: continue
                    if sum(t >> (Z | 1 << u) & 1 for u in R) >= 2: hit = True; break
                if hit: break
            if hit: break
        if hit: out.add(k)
    return out
def demorgan(n, G, outs, which):
    # rebuild the gate list, replacing the OR gates in `which` by NOT(AND(NOT a, NOT b))
    newG = []; pos = {}
    def wire(x): return x if x < n else pos[x]
    for k, g in enumerate(G):
        if g[0] == 'or' and k in which:
            a, b = wire(g[1]), wire(g[2])
            newG.append(['not', a]); na = n + len(newG) - 1
            newG.append(['not', b]); nb = n + len(newG) - 1
            newG.append(['and', na, nb]); c = n + len(newG) - 1
            newG.append(['not', c])
        elif g[0] == 'not': newG.append(['not', wire(g[1])])
        else: newG.append([g[0], wire(g[1]), wire(g[2])])
        pos[n + k] = n + len(newG) - 1
    return newG, [wire(o) for o in outs]
random.seed(3)
print("| circuit | n | base | NOT gates | gates | OR-only witnesses | any-gate witnesses | any-gate >= base |"); print("|---|---|---|---|---|---|---|---|")
bad = tot = 0
for f in sorted(glob.glob('research/one-not/data/witnesses/*.json')):
    d = json.load(open(f)); n, S, G, outs = d['n'], d['sets'], d['gates'], d['outs']
    if n > 9: continue
    assert correct(n, S, G, outs)
    base = sum(len(R) - 1 for R in S); ors = [k for k, g in enumerate(G) if g[0] == 'or']
    for frac in (0, 0.5, 1):
        which = set(random.sample(ors, int(len(ors) * frac)))
        G2, o2 = demorgan(n, G, outs, which)
        assert correct(n, S, G2, o2)
        a = len(witness(n, S, G2, True)); b = len(witness(n, S, G2, False)); tot += 1; bad += b < base
        print(f"| {os.path.basename(f)} | {n} | {base} | {sum(g[0]=='not' for g in G2)} | {len(G2)} | {a} | {b} | {b >= base} |")
print(f"instances {tot}, any-gate count below base: {bad}")
