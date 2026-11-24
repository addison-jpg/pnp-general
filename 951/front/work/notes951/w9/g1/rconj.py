import sys
from g1lib import *
for f in sys.argv[1:]:
    cs=[c for c in load(f) if c['n']<=12]; mn=99; arg=None; nv1=0;viol=0
    for c in cs:
        n=c['n']; s=len(c['gates']); b=base(c['sets'])
        D=0; V1=0
        for v in range(n):
            d=deg(c,v); R=readers(c,v)
            if d==0: continue
            D+=max(0,d-len(R))
            if len(R)==1 and d>=2:
                V1+=1; g=c['gates'][R[0]-n]
                if g[0]=='not' or all(a<n for a in g[1:]): viol+=1
        nv1+=V1
        if s-b-D<mn: mn=s-b-D; arg=(s,b,D,V1)
    print(f.split('/')[-1],len(cs),'min slack-Delta',mn,arg,'total single-reader vars',nv1,'P2 violations',viol)
