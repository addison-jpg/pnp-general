import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2lib import *
CS=corpus(9)
for s in range(int(sys.argv[1]),int(sys.argv[2])): CS+=randgen(s,3000)
st=collections.Counter(); ex={}
def feats(c,Q,F,r):
    n=c['n']; P=list(r); G=c['G']
    ors=[n+k for k,g in enumerate(G) if g[0]=='or']
    f={}
    for nm,W,dom in (('tF real',c['W'],F),('tF C0',c['W0'],F),('tF C1',c['W1'],F),('tOR real',c['W'],ors),('tOR C0',c['W0'],ors),('tOR C1',c['W1'],ors)):
        f[nm]={v:sum(1 for g in dom if bit(W[g],Q|1<<v) and not bit(W[g],Q)) for v in P}
    return f
for c in CS:
    for Q in range(1<<c['n']):
        if not aliveW(c,Q): continue
        cb=cube(c,Q); hh=c['h']&cb; mono=hh in (0,cb)
        F,r=stepinfo(c,Q); st['inst',mono]+=1
        for nm,t in feats(c,Q,F,r).items():
            for var,key in (('max',lambda v:t[v]),('max t-cost',lambda v:t[v]-r[v][1])):
                m=max(key(v) for v in r); A=[v for v in r if key(v)==m]
                if any(r[v][0]<r[v][1] for v in A): st[nm,var,'some argmax bad',mono]+=1; ex.setdefault((nm,var,'some argmax bad',mono),(c['name'],Q,A))
                if all(r[v][0]<r[v][1] for v in A): st[nm,var,'ALL argmax bad',mono]+=1
            if nm=='tF real' and not any(t[v]>=r[v][1] for v in r): st['no v with t>=cost',mono]+=1
for k in sorted(st,key=str): print(k,st[k],ex.get(k))
