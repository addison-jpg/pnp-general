# find systems where rule q (or p) is decisive in feasible() itself (all deletions covered under both rule sets)
import pickle, sys
from cover import norm, degs, delete
from cover2 import covered, feasible, info
L=pickle.load(open('pairsys8.pkl','rb'))
k=0
for s,np_ in L:
    S=norm(s)
    a=covered(S,'245p','none'); b=covered(S,'245pq','none')
    if b and not a and all(covered(delete(S,v),'245p','none') for v in degs(S)):
        d,pts,Sv,l,P=info(S)
        print([sorted(x) for x in S]); print(' deg',d,' lines',l,' pairs',{v:sorted(P[v]) for v in pts if P[v]})
        print(' 245p scenarios:',feasible(S,True,'245p','none'))
        k+=1
        if k>=3: break
