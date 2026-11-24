"""Free-candidate test on CANONICAL families: world-1 candidate at z = 0, world-0 candidates at the minimal points z with
h(z) = 1 (z vanishing on S_w, minimal under <=). Every output needs a canonical candidate disjoint from all canonical
candidates of all other outputs. Also report whether choosing those free candidates is an SDR (it is, by definition)."""
import sys, json
from mzmatroid import evaluate, merge_set
tot = 0; ok = 0; inst = 0
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    hw = gates[[k for k, g in enumerate(gates) if g[0] == 'not'][0]][1]
    hval = [evaluate(n, gates, z)[hw] for z in range(1 << n)]
    C = []
    for S in sets:
        Sm = sum(1 << u for u in S)
        w0 = [z for z in range(1 << n) if not z & Sm and hval[z] == 1]
        mins = [z for z in w0 if not any(y != z and (y & z) == y for y in w0)]
        cand = {merge_set(n, gates, S, 0): 'w1@0'}
        for z in mins: cand.setdefault(merge_set(n, gates, S, z), 'w0min')
        C.append(cand)
    res = []; allok = True
    for w, F in enumerate(C):
        others = set().union(*[M for v, G in enumerate(C) if v != w for M in G])
        free = [F[M] for M in F if not (M & others)]
        tot += 1; ok += bool(free); allok &= bool(free)
        res.append(f"{len(F)}c:{'free ' + ','.join(sorted(set(free))) if free else 'NONE'}")
    inst += allok
    print(f.split('/')[-1], '|', ' ; '.join(res))
print(f'outputs with a free canonical candidate: {ok}/{tot}; instances all free: {inst}/{len(sys.argv)-1}')
