"""Free-candidate test: does every output w have a merge set M_z(w) disjoint from EVERY merge set of EVERY other output?
Also the weaker per-world version and, if not free, how many other outputs' sets it must avoid."""
import sys, json
from mzmatroid import evaluate, merge_set
tot = 0; free_all = 0; inst_all = 0
for f in sys.argv[1:]:
    d = json.load(open(f)); n, gates, sets = d['n'], d['gates'], d['sets']
    hw = gates[[k for k, g in enumerate(gates) if g[0] == 'not'][0]][1]
    V = []; W = []
    for S in sets:
        Sm = sum(1 << u for u in S); F = {}
        for z in range(1 << n):
            if z & Sm: continue
            F.setdefault(merge_set(n, gates, S, z), set()).add(0 if evaluate(n, gates, z)[hw] == 1 else 1)
        V.append(F)
    res = []; ok_inst = True
    for w, F in enumerate(V):
        others = set().union(*[M for v, G in enumerate(V) if v != w for M in G]) if len(V) > 1 else set()
        free = [ (sorted(M), sorted(F[M])) for M in F if not (M & others)]
        tot += 1; free_all += bool(free); ok_inst &= bool(free)
        res.append('free' + str([wl for _, wl in free][:2]) if free else 'NONE')
    inst_all += ok_inst
    print(f.split('/')[-1], '|', ' ; '.join(res))
print(f'outputs with a free candidate: {free_all}/{tot}; instances where every output has one: {inst_all}/{len(sys.argv)-1}')
