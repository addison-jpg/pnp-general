from bt import *
def maxflow_match(dem, adj):
    # dem: list of demands per set; adj: list of sets of gates; gate cap 1. returns matched total
    match={}  # gate->(set)
    def aug(w,seen):
        for g in adj[w]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g],seen):
                match[g]=w; return True
        return False
    tot=0
    for w,d in enumerate(dem):
        for _ in range(d):
            if aug(w,set()): tot+=1
    return tot
def classes(T,b):
    """world b: b=1 -> C1 on U0; b=0 -> C0 on U1; b='real' -> real on all"""
    if b=='real': Dom=T.FULL; w=T.w['real']
    else: Dom=T.U0 if b==1 else T.U1; w=T.w[b]
    n=T.n; sets=T.c['sets']; o=[x&Dom for x in T.o]
    D=[];P=[]
    for wi,S in enumerate(sets):
        d=set();p=set()
        for g in range(n,T.W):
            gv=w[g]&Dom
            if gv & ~o[wi]==0:
                L=[u for u in S if T.var[u]&Dom and (T.var[u]&Dom&~gv)==0]
                if len(L)>=2: d.add(g)
            if o[wi]&~gv==0 and gv!=Dom and all(o[j]&~gv for j in range(len(sets)) if j!=wi):
                p.add(g)
        D.append(d);P.append(p)
    return D,P
