# full lifted single-domain menu (circuit-dependent zeros/ones of F_w) + ClassFrac LP
from sl import *
from chk2 import lp
import sys, collections
def minimal_pts(T,wi,u,Q,cap=3):
    # minimal p with p∩Q={u}, F_w(p,0)=1
    n=T.n; rest=[v for v in range(n) if v not in Q]; out=[]; Fw0=T.w[0][T.c['outs'][wi]]
    for r in range(len(rest)+1):
        for zz in itertools.combinations(rest,r):
            p=(1<<u)|sum(1<<v for v in zz)
            if (Fw0>>p)&1 and not any((q&p)==q for q in out): out.append(p)
        if len(out)>=cap or r>=3: break
    return out[:cap]
def menu(T,c,wi,capc=40,capcombo=128):
    n=T.n; R=c['sets'][wi]; d=len(R)-1; gates=range(n,T.W); no=T.FULL^T.o[wi]; o=T.c['outs'][wi]
    cls={}
    def add(base_ok,ats,tag):
        # ats: dict u->list of atoms (p,l)
        combos=itertools.islice(itertools.product(*[ats[u] for u in R]),capcombo)
        for cb in combos:
            if tag[0]=='0' and sum(1 for a in cb if a[1]==1)>1: continue
            cl=frozenset(g for g in base_ok if sum((T.w[a[1]][g]>>a[0])&1 for a in cb)>=2)
            assert len(cl)>=d,(tag,cb)
            cls.setdefault(cl,(tag,cb))
    # type 0
    G0=[g for g in gates if (T.w[0][g]&no)==0]
    ats={u:[(p,0) for p in minimal_pts(T,wi,u,R)]+[(1<<u,1)] for u in R}
    if sum(1 for u in R if len(ats[u])==1)<=1: add(G0,ats,('0',))
    # type 1: maximal c with F_w(c,1)=0
    rest=[v for v in range(n) if v not in R]; F1=T.w[1][o]; cs=[]
    for r in range(len(rest),-1,-1):
        for zz in itertools.combinations(rest,r):
            cc=sum(1<<v for v in zz)
            if not (F1>>cc)&1 and not any((cc&q)==cc for q in cs): cs.append(cc)
    for cc in cs[:capc]:
        Q=[v for v in range(n) if not cc>>v&1]
        G1=[g for g in gates if not (T.w[1][g]>>cc)&1]
        ats={u:[(1<<u,1)]+[(p,0) for p in minimal_pts(T,wi,u,Q)] for u in R}
        add(G1,ats,('1',cc))
    ks=[x for x in cls if not any(y<x for y in cls)]
    return ks,[cls[x] for x in ks]
def run(name,c,verbose=False):
    T=TT(c); assert T.correct()
    dem=[len(s)-1 for s in c['sets']]; opts=[];info=[]
    for wi in range(len(dem)):
        k,i=menu(T,c,wi); opts.append(k); info.append(i)
    L,pi,lam=lp(dem,opts)
    if verbose:
        print(name,'L*',round(L,4),'menu',[len(o) for o in opts])
        print(' pi',{g:round(p,3) for g,p in pi.items() if p>1e-9})
        for (w,j),x in sorted(lam.items()): print('  set',w,'lam',round(x,3),info[w][j][0],sorted(opts[w][j]))
    return L
if __name__=='__main__':
    if len(sys.argv)>1:
        for f in sys.argv[1:]: run(f,load(f)[0],True)
    else:
        cs=allcirc(); res=[]
        for name,c in cs:
            if c['n']>9: continue
            res.append((run(name,c),name))
        res.sort(reverse=True); print(len(res),res[:6]); print(collections.Counter(round(L,3) for L,_ in res).most_common(8))
