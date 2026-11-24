"""Layer-cake gap per WORLD: families F_w^0 (h(z)=1) and F_w^1 (h(z)=0) separately."""
import sys, json, itertools, random
from mzmatroid import evaluate, merge_set
random.seed(5); stats = {0: [0, 0], 1: [0, 0]}
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    nots = [k for k, g in enumerate(gates) if g[0] == 'not']; hw = gates[nots[0]][1]
    fams = {0: [], 1: []}
    for S in sets:
        Sm = sum(1 << u for u in S); F = {0: set(), 1: set()}
        for z in range(1 << n):
            if z & Sm: continue
            F[0 if evaluate(n, gates, z)[hw] == 1 else 1].add(merge_set(n, gates, S, z))
        for e in (0, 1):
            if F[e]: fams[e].append(sorted(F[e], key=sorted))
    allM = [M for e in (0, 1) for F in fams[e] for M in F]; G = range(len(gates))
    chains = [[M1 | M2, M1] for M1, M2 in itertools.product(allM, repeat=2)]
    for _ in range(300):
        ms = random.sample(allM, min(len(allM), 3)); U = set(); ch = []
        for M in ms: U |= M; ch.append(frozenset(U))
        chains.append(list(reversed(ch)))
    out = []
    for e in (0, 1):
        gaps = []
        for F in fams[e]:
            g = 0
            for ch in chains[:2500]:
                ch = [frozenset(A) for A in ch]; pi = [sum(1 for A in ch if x in A) for x in G]
                g = max(g, min(sum(pi[x] for x in M) for M in F) - sum(min(len(M & A) for M in F) for A in ch))
            gaps.append(g); stats[e][0] += g > 0; stats[e][1] += 1
        out.append(f"w{e}:{gaps}")
    print(f.split('/')[-1], ' '.join(out))
print('families with positive layer-cake gap: world0', stats[0], 'world1', stats[1])
