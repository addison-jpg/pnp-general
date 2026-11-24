from cls2 import *
def explore(T,wi,b):
    """RM exploration; returns set of explored OR gates with |B|>=2 (E2 region), and B function"""
    n=T.n; S=T.c['sets'][wi]
    if b==1: Dom=T.U0; w=T.w[1]; atoms=[u for u in S if not (T.h>>(1<<u))&1]; pts={u:1<<u for u in atoms}
    else:
        Dom=T.U1; w=T.w[0]; z=sum(1<<v for v in range(n) if v not in S); atoms=list(S); pts={u:z|1<<u for u in S}
    o=T.o[wi]&Dom
    B=lambda g: frozenset(u for u in atoms if w[g]>>pts[u]&1)
    root=T.c['outs'][wi]
    # exploration: Lambda set; process gates top-down
    Lam={root}; explored=set(); child={}
    stack=[root]
    while stack:
        g=stack.pop()
        if g<n or g in explored: continue
        explored.add(g)
        G=T.G[g-n]
        if G[0]=='or': ch=[G[1],G[2]]
        elif G[0]=='not': ch=[]
        else:
            R=0
            for x in Lam:
                if x!=g: R|=w[x]
            s,t=G[1],G[2]
            if (R|w[s])&Dom==o: ch=[s]
            elif (R|w[t])&Dom==o: ch=[t]
            else: return None  # RM failed
        Lam.discard(g); Lam|=set(ch); child[g]=ch
        stack+=ch
    # E2
    E2=set(); st=[root]
    while st:
        g=st.pop()
        if g<n or g in E2 or len(B(g))<2: continue
        E2.add(g); st+=child.get(g,[])
    ors={g for g in E2 if T.G[g-n][0]=='or'}
    return ors,len(atoms)
