# smallest essential one-NOT circuits for a system, h free (h(0)=0, given sets hard), one run at a time
import sys, json, time
from satgen import *
n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); s=int(sys.argv[3]); pn=[int(v) for v in sys.argv[4].split(',')]
tmax=int(sys.argv[5]) if len(sys.argv)>5 else 280; nsol=int(sys.argv[6]) if len(sys.argv)>6 else 1
tag=sys.argv[7] if len(sys.argv)>7 else 'free'
hard=[True]*len(sets)
z=lambda S: tuple(0 if v in S else 1 for v in range(n))
hc=[(tuple([0]*n),0)]+[(z(S),1) for S in sets]
if tag=='th2like':
    for v in range(n): hc.append((tuple(int(i==v) for i in range(n)),0))
    for S in sets:
        for a in S:
            for b in S:
                if a<b: hc.append((tuple(int(i in (a,b)) for i in range(n)),1))
for pnot in pn:
    st,sols,t,tb,ncl=solve(n,sets,s,pnot,tmax=tmax,nsol=nsol,hcons=hc)
    print('s',s,'pnot',pnot,st,'nsol',len(sols),'sec %.1f build %.1f'%(t,tb),'clauses',ncl,flush=True)
    for c in sols: print('SOL',json.dumps(c),flush=True)
