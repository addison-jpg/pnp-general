import json, itertools
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def load(f):
    if f.endswith('.json'): return [norm(json.load(open(f)))]
    return [norm(json.loads(l)) for l in open(f) if l.strip()]
def ev(n,G,x,force=None):
    w=list(x)
    for g in G:
        if g[0]=='not': w.append((1-w[g[1]]) if force is None else force)
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
def nw(c): return c['n']+[k for k,g in enumerate(c['gates']) if g[0]=='not'][0]
def hw(c): return [g[1] for g in c['gates'] if g[0]=='not'][0]
def verify(c):
    n,G=c['n'],c['gates']; ok=True; c0w=c1w=False
    for x in itertools.product([0,1],repeat=n):
        w=ev(n,G,x); w0=ev(n,G,x,0); w1=ev(n,G,x,1)
        for S,o in zip(c['sets'],c['outs']):
            t=int(any(x[u] for u in S))
            if w[o]!=t: ok=False
            if w0[o]!=t: c0w=True
            if w1[o]!=t: c1w=True
    return ok,c0w,c1w
def system(c,S,z,atoms):
    """atoms: dict u->point. returns (good, wz, B) B[i]=frozenset of u with wire true at atom, for wires zero at z"""
    n,G=c['n'],c['gates']; N=nw(c); wz=ev(n,G,z)
    at={u:ev(n,G,atoms[u]) for u in S}
    good = wz[N]==1 or sum(at[u][N] for u in S)<=1
    B={i:frozenset(u for u in S if at[u][i]) for i in range(n+len(G)) if wz[i]==0}
    return good,wz,B
def merges(c,S,B):
    """bottom-up union-find over gates in order; returns list of (gate, blockA, blockB), counted set"""
    n,G=c['n'],c['gates']; par={u:u for u in S}
    def f(u):
        while par[u]!=u: u=par[u]
        return u
    M=[]; cnt=[]
    for i in range(n,n+len(G)):
        if i not in B: continue
        b=B[i]
        if len(b)>=2: cnt.append(i)
        r=sorted({f(u) for u in b})
        if len(r)>=2:
            assert len(r)==2,(i,r)
            M.append(i); par[r[1]]=r[0]
    assert len({f(u) for u in S})==1
    return M,cnt
def zQ(n,Q): return [0 if v in Q else 1 for v in range(n)]
def unit(n,u): return [int(v==u) for v in range(n)]
def plus(z,u):
    p=list(z); p[u]=1; return p
