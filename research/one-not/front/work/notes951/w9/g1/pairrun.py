# pairrun.py: (gen) rebuild EXACTLY the pair-core list of paircores.py (n=8: all; n=9: random sample, seed 7) and pickle it;
#             (eval) coverage table by #pairs for given greedy mode / rule sets.
# usage: python3 pairrun.py gen N        -> pairsys{N}.pkl  (list of (system, #pairs))
#        python3 pairrun.py eval N GREEDY RULES1,RULES2 [lo hi]   (slice of the list, for split runs)
import pickle, itertools, random, sys
from cover import norm
from enumcores import canon
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
if sys.argv[1]=='gen':
    random.seed(7)
    n=int(sys.argv[2]); R=pickle.load(open(f'cores{n}.pkl','rb'))
    seen=set(); L=[]
    for sk in R:
        for s in aug(n,sk,full=(n==8),samples=60):
            f=canon(n,[frozenset(S) for S in s])
            if f in seen: continue
            seen.add(f); L.append((s,len(s)-len(sk)))
    pickle.dump(L,open(f'pairsys{n}.pkl','wb')); print('n',n,'pair systems',len(L))
else:
    from cover2 import covered
    n=int(sys.argv[2]); gr=sys.argv[3]; RS=sys.argv[4].split(',')
    L=pickle.load(open(f'pairsys{n}.pkl','rb'))
    lo,hi=(int(sys.argv[5]),int(sys.argv[6])) if len(sys.argv)>6 else (0,len(L))
    for rules in RS:
        tot=cv=0; bp={}; res=[]
        for s,k in L[lo:hi]:
            c=covered(s,rules,gr); tot+=1; cv+=c; a=bp.setdefault(k,[0,0]); a[0]+=1; a[1]+=c; res.append(c)
        print('n',n,'slice',lo,hi,'greedy',gr,'rules',rules,'total',tot,'covered',cv,flush=True)
        print(' by #pairs (total,covered):',sorted(bp.items()),flush=True)
        pickle.dump(res,open(f'pairres{n}_{gr}_{rules}_{lo}_{hi}.pkl','wb'))
