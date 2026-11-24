from cls import *
def classes2(T):
    """returns dict name -> list per set of gate sets. names: Dr,Pr (T3 real), D0,P0 (world0, hard sets only), D1,P1 (world1)"""
    n=T.n; sets=T.c['sets']; m=len(sets); out={}
    hard=[T.o[i]|T.U0!=T.FULL for i in range(m)]  # o_w not identically 1 on U1  <=> h(z_S)=1
    for name,Dom,w,act in (('r',T.FULL,T.w['real'],[True]*m),('0',T.U1,T.w[0],hard),('1',T.U0,T.w[1],[True]*m)):
        o=[x&Dom for x in T.o]
        D=[set() for _ in range(m)];P=[set() for _ in range(m)]
        for wi,S in enumerate(sets):
            if not act[wi]: continue
            for g in range(n,T.W):
                gv=w[g]&Dom
                if gv&~o[wi]==0:
                    L=[u for u in S if T.var[u]&Dom and (T.var[u]&Dom&~gv)==0]
                    if len(L)>=2: D[wi].add(g)
                if o[wi]&~gv==0 and gv!=Dom and all(o[j]&~gv for j in range(m) if j!=wi and act[j]):
                    P[wi].add(g)
        out['D'+name]=D; out['P'+name]=P
    out['hard']=hard
    return out
