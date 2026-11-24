from wl import *
import lift
def minimal_pts_full(T,wi,u,Q,cap=50):
    n=T.n; rest=[v for v in range(n) if v not in Q]; out=[]; Fw0=T.w[0][T.c['outs'][wi]]
    for r in range(len(rest)+1):
        for zz in itertools.combinations(rest,r):
            p=(1<<u)|sum(1<<v for v in zz)
            if (Fw0>>p)&1 and not any((q&p)==q for q in out): out.append(p)
    return out[:cap]
lift.minimal_pts=minimal_pts_full
name=sys.argv[1]; c=load(name)[0]; T=TT(c); dem=[len(s)-1 for s in c['sets']]
opts=[lift.menu(T,c,wi,capc=10**6,capcombo=int(sys.argv[2]))[0] for wi in range(len(dem))]
print([len(o) for o in opts])
print(wlp(dem,opts)[0],wlp(dem,opts,True)[0],sum(dem))
