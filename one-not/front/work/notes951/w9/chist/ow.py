# one-world ClassFrac: L* restricted to type-0-only / type-1-only lifted menus (sub-selection LP of chk2.lp)
from wl import *
def menu_t(T,c,wi,types='01',lvl0in1=True,capc=40,capcombo=128):
    n=T.n; R=c['sets'][wi]; d=len(R)-1; gates=range(n,T.W); no=T.FULL^T.o[wi]; o=T.c['outs'][wi]
    cls={}
    def add(base_ok,ats,tag):
        for cb in itertools.islice(itertools.product(*[ats[u] for u in R]),capcombo):
            if tag[0]=='0' and sum(1 for a in cb if a[1]==1)>1: continue
            cl=frozenset(g for g in base_ok if sum((T.w[a[1]][g]>>a[0])&1 for a in cb)>=2)
            assert len(cl)>=d
            cls.setdefault(cl,(tag,cb))
    if '0' in types:
        G0=[g for g in gates if (T.w[0][g]&no)==0]
        ats={u:[(p,0) for p in minimal_pts(T,wi,u,R)]+[(1<<u,1)] for u in R}
        if sum(1 for u in R if len(ats[u])==1)<=1: add(G0,ats,('0',))
    if '1' in types:
        rest=[v for v in range(n) if v not in R]; F1=T.w[1][o]; cs=[]
        for r in range(len(rest),-1,-1):
            for zz in itertools.combinations(rest,r):
                cc=sum(1<<v for v in zz)
                if not (F1>>cc)&1 and not any((cc&q)==cc for q in cs): cs.append(cc)
        for cc in cs[:capc]:
            Q=[v for v in range(n) if not cc>>v&1]
            G1=[g for g in gates if not (T.w[1][g]>>cc)&1]
            ats={u:[(1<<u,1)]+([(p,0) for p in minimal_pts(T,wi,u,Q)] if lvl0in1 else []) for u in R}
            add(G1,ats,('1',cc))
    ks=[x for x in cls if not any(y<x for y in cls)]
    return ks,[cls[x] for x in ks]
def run1(name,c):
    T=TT(c)
    if not T.correct(): return None
    dem=[len(s)-1 for s in c['sets']]; out=[]
    for types,l0 in (('01',True),('0',True),('1',True),('1',False)):
        o=[menu_t(T,c,wi,types,l0)[0] for wi in range(len(dem))]
        out.append(9.0 if any(len(x)==0 for x in o) else lp(dem,o)[0])
    return out
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    cs=[(n,c) for n,c in allcirc()+extra() if lo<=c['n']<=hi and any(g[0]=='not' for g in c['gates'])]
    st=collections.Counter(); bad=[]
    for name,c in cs:
        r=run1(name,c)
        if r is None: continue
        k=tuple(x<=1+1e-7 for x in r); st[k]+=1
        if not k[1] and not k[2]: bad.append((name,c['n'],[round(x,3) for x in r]))
        if hi>7: print(name,c['n'],[round(x,3) for x in r],flush=True)
    print('(all,t0,t1,t1 pure unit atoms) <=1:',st); print(len(bad),bad[:30])
