from cls3 import *
def d0p(T,wi):
    n=T.n; S=T.c['sets'][wi]; Dom=T.U1; w=T.w[0]; o=T.o[wi]&Dom
    z=sum(1<<v for v in range(n) if v not in S)
    return {g for g in range(n,T.W) if (w[g]&Dom&~o)==0 and sum(w[g]>>(z|1<<u)&1 for u in S)>=2}
def allcls(T):
    C=classes2(T); m=len(T.c['sets'])
    C['D0p']=[d0p(T,i) if C['hard'][i] else set() for i in range(m)]
    C['D1e']=[C['D1'][i] if not C['hard'][i] else set() for i in range(m)]
    return C
