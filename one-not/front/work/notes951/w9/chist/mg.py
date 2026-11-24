# merge-set FracMatch: classes := canonical union-find merge sets M_z(w) (circuit order) on the real B3 menu; whole-class LP == sub-selection LP
from cxU3 import *
def merges(c,T=None):
    T=T or TT(c); n=T.n; W=T.w['real']; G=c['gates']; out=[]; anom=0
    nb=max(1,(1<<n)//8); tb=[w.to_bytes(nb,'little') for w in W]
    bit=lambda g,z: (tb[g][z>>3]>>(z&7))&1
    for wi,R in enumerate(c['sets']):
        rest=[v for v in range(n) if v not in R]; m={}
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                par={u:u for u in R}
                def find(u):
                    while par[u]!=u: par[u]=par[par[u]]; u=par[u]
                    return u
                B=[None]*len(W); M=[]
                for v in range(n): B[v]=frozenset([v]) if v in R else frozenset()
                for k,g in enumerate(G):
                    i=n+k
                    if bit(i,z): continue
                    B[i]=frozenset(u for u in R if bit(i,z|1<<u))
                    if g[0]=='or':
                        a,b=B[g[1]],B[g[2]]
                        if a and b:
                            ra,rb=find(next(iter(a))),find(next(iter(b)))
                            if ra!=rb: par[ra]=rb; M.append(i)
                    if len({find(u) for u in B[i]})>1: anom+=1
                if len(M)!=len(R)-1: anom+=1
                m[z]=frozenset(M)
        out.append(m)
    return out,anom
def run(name,c):
    T=TT(c)
    if not T.correct(): return None
    dem=[len(s)-1 for s in c['sets']]; Ms,anom=merges(c,T)
    ents=[]
    for w,m in enumerate(Ms):
        for cl in set(m.values()):
            if len(cl)>=dem[w]: ents.append((w,cl,None))
    if any(not any(e[0]==w for e in ents) for w in range(len(dem))): return 9.0,anom
    return maxload(dem,ents),anom
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    cs=[(n,c) for n,c in allcirc()+extra() if lo<=c['n']<=hi and any(g[0]=='not' for g in c['gates'])]
    st=collections.Counter(); an=0; bad=[]
    for name,c in cs:
        r=run(name,c)
        if r is None: continue
        L,a=r; an+=a>0; st[L<=1+1e-7]+=1
        if L>1+1e-7: bad.append((name,c['n'],round(L,3)))
        if hi>7: print(name,c['n'],round(L,3),'anom',a,flush=True)
    print(st,'circuits with anomalies',an,bad[:20])
