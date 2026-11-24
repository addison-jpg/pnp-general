import pickle, itertools, random, sys
from cover2 import covered
from cover import norm
from enumcores import canon
random.seed(7)
def aug(n,sk,full=True,samples=0):
    lines=[frozenset(S) for S in sk]
    free=[p for p in itertools.combinations(range(n),2) if not any(set(p)<=S for S in lines)]
    if full:
        for r in range(1,len(free)+1):
            for ps in itertools.combinations(free,r): yield sk+[list(p) for p in ps]
    else:
        for _ in range(samples):
            ps=[p for p in free if random.random()<random.choice([0.1,0.3,0.5])]
            if ps: yield sk+[list(p) for p in ps]
n=int(sys.argv[1]); R=pickle.load(open(f'cores{n}.pkl','rb'))
seen=set(); tot=cv=0; bypairs={}
for sk in R:
    for s in aug(n,sk,full=(n==8),samples=60):
        f=canon(n,[frozenset(S) for S in s])
        if f in seen: continue
        seen.add(f); tot+=1
        c=covered(s); cv+=c
        k=len(s)-len(sk); a=bypairs.setdefault(k,[0,0]); a[0]+=1; a[1]+=c
print('n',n,'cores with >=1 pair-set (up to iso%s):'%('' if n==8 else ', random sample'),tot,'covered',cv)
print(' by #pairs (total,covered):',sorted(bypairs.items()))
