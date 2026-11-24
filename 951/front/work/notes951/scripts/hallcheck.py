# Matching (Hall) version of the charging: canonical test system per set = smallest Good zero set Q ⊇ S
# (cone-restricted, unit test points). Build bipartite graph sets -> counted gates; each set demands |S|-1
# distinct gates (Lemma G guarantees |D| >= |S|-1). Max b-matching == base  <=>  Hall's condition holds.
import json, itertools, sys, chargeok_check as K, conedbl
from collections import Counter
def canon(c):
    n,S,G,outs=c['n'],[set(x) for x in c['sets']],c['gates'],c['outs']
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    ev=lambda x: K.evaluate(n,G,list(x))
    unit=[ev([int(v==u) for v in range(n)]) for u in range(n)]
    du=all(unit[u][nw]==0 for u in range(n))
    Ds=[]
    for wi,R in enumerate(S):
        cone=K.cone(n,G,outs[wi]); best=None
        rest=[v for v in range(n) if v not in R]
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=R|set(ex); z=ev([0 if v in Q else 1 for v in range(n)])
                if nw in cone and not (z[nw]==1 or du): continue
                best=[i for i in sorted(cone) if z[i]==0 and sum(unit[u][i] for u in R)>=2]; break
            if best is not None: break
        Ds.append(best)
    return Ds
def bmatch(Ds, demand):
    # augmenting paths: copy each set 'demand' times, match to gates
    slots=[(i,k) for i in range(len(Ds)) for k in range(demand[i])]
    owner={}
    def aug(slot, seen):
        i,_=slot
        for g in Ds[i]:
            if g in seen: continue
            seen.add(g)
            if g not in owner or aug(owner[g], seen):
                owner[g]=slot; return True
        return False
    return sum(1 for sl in slots if aug(sl,set()))
H=Counter(); fails=[]
for f in sys.argv[1:]:
    for l in open(f):
        c=conedbl.norm(json.loads(l)); Ds=canon(c)
        demand=[len(s)-1 for s in c['sets']]; base=sum(demand)
        sz=[len(d) for d in Ds]
        H['n']+=1
        disjoint = len(set().union(*map(set,Ds)))==sum(sz)
        H['disjoint (Gap-G with canonical choice)']+=disjoint
        got=bmatch(Ds,demand); ok = got==base
        H['Hall/matching OK']+=ok
        if not ok and len(fails)<3: fails.append((c,Ds,got,base))
print(dict(H))
for c,Ds,got,base in fails: print('MATCH FAIL matched',got,'base',base,'D',Ds,json.dumps(c))
