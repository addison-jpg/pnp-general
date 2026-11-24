"""Split {M_z(w)} by world: world0 = zero points with h(z)=1 (NOT outputs 0), world1 = h(z)=0. Test basis exchange per world."""
import sys, json
from mzmatroid import evaluate, merge_set, is_exchange_family
tot = {'w0': [0, 0], 'w1': [0, 0], 'all': [0, 0]}; cross = 0; nsets = 0
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    nots = [k for k, g in enumerate(gates) if g[0] == 'not']
    if len(nots) != 1: print(f, 'NOT count', len(nots)); continue
    hwire = gates[nots[0]][1]
    row = []
    for S in sets:
        Smask = sum(1 << u for u in S); F = {0: set(), 1: set()}
        for z in range(1 << n):
            if z & Smask: continue
            hz = evaluate(n, gates, z)[hwire]
            F[0 if hz == 1 else 1].add(merge_set(n, gates, S, z))
        res = []
        for key, wk in ((0, 'w0'), (1, 'w1')):
            if F[key]:
                ok = is_exchange_family(list(F[key]))[0]; tot[wk][0] += ok; tot[wk][1] += 1; res.append(f"{wk}:{len(F[key])}{'' if ok else '!'}")
        allok = is_exchange_family(list(F[0] | F[1]))[0]; tot['all'][0] += allok; tot['all'][1] += 1
        inter = (set().union(*F[0]) & set().union(*F[1])) if F[0] and F[1] else set()
        cross += bool(inter); nsets += 1
        row.append(' '.join(res) + f" cross={len(inter)}")
    print(f.split('/')[-1], '|', ' ; '.join(row))
print('exchange holds (sets): world0', tot['w0'], 'world1', tot['w1'], 'both worlds together', tot['all'],
      '| sets whose world0 and world1 merge gates intersect:', cross, 'of', nsets)
