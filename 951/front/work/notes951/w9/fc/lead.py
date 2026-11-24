# coordinator's lead: h = pq v rs (non-singleton minterms), >=3 sets, one of size >=4. Function-level scan: which (sets,h) have NO
# pairwise-separated system family among the big sets (compat.famsearch)?  Only those can host a free-choice counterexample (C3c).
import itertools, sys, time
from compat import famsearch
SYS={'A':(7,[(0,1,2,3),(0,4,5),(1,4,6)]),'B':(7,[(0,1,2,3),(0,4,5),(1,4,6),(2,5,6)]),'C':(7,[(0,1,2,3),(0,4,5,6)]),
     'D':(8,[(0,1,2,3),(0,4,5,6),(1,4,7)]),'E':(8,[(0,1,2,3),(4,5,6,7),(0,4)]) ,'F':(7,[(0,1,2,3),(3,4,5),(5,6,0)])}
t0=time.time()
for name in sys.argv[1:]:
    n,sets=SYS[name]; pairs=list(itertools.combinations(range(n),2)); tot=0; bad=[]
    for k in (2,3):
        for ms in itertools.combinations(pairs,k):
            if time.time()-t0>240: break
            masks=[(1<<a)|(1<<b) for a,b in ms]
            hf=lambda x,masks=masks: int(any(x&m==m for m in masks))
            # need >=2 hard sets to be in the sorry's case
            hard=sum(hf(sum(1<<v for v in range(n) if v not in S)) for S in sets)
            if hard<2: continue
            tot+=1; fam,sz=famsearch(n,sets,hf)
            if fam is None: bad.append(ms)
        print(name,sets,'h = OR of',k,'pair-minterms: tested',tot,'obstructed (no separated family):',len(bad),bad[:6],flush=True)
