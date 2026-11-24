# Two-world Hall toolkit. Dc = canonical (hallcheck.canon semantics: smallest Good Q ⊇ S, cone-restricted, unit atoms)
# Dr = R* (z_S, unit atoms, all gates).
import json, itertools, sys
from collections import Counter
def ev(n,G,x,force=None):
    w=list(x)
    for g in G:
        if g[0]=='not': w.append((1-w[g[1]]) if force is None else force)
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
def cone(n,G,o):
    seen,st=set(),[o]
    while st:
        i=st.pop()
        if i in seen: continue
        seen.add(i)
        if i>=n: st.extend(G[i-n][1:])
    return {i for i in seen if i>=n}
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def cnt(n,G,S,z,K=None,unit=False):
    wz=ev(n,G,z); at=[]
    for u in S:
        p=[0]*n if unit else list(z); p[u]=1; at.append(ev(n,G,p))
    rng=range(n,n+len(G)) if K is None else sorted(K)
    return [i for i in rng if wz[i]==0 and sum(a[i] for a in at)>=2]
def canonQ(c):
    n,G=c['n'],c['gates']; nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    unit=[ev(n,G,[int(v==u) for v in range(n)]) for u in range(n)]
    du=all(unit[u][nw]==0 for u in range(n)); res=[]
    for wi,S in enumerate(c['sets']):
        R=set(S); co=cone(n,G,c['outs'][wi]); rest=[v for v in range(n) if v not in R]; found=None
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=R|set(ex); z=[0 if v in Q else 1 for v in range(n)]
                if nw in co and not (ev(n,G,z)[nw]==1 or du): continue
                found=(Q,z,co); break
            if found: break
        res.append(found)
    return res
def worlds(c):
    n,G=c['n'],c['gates']; Dc=[];Dr=[]
    for wi,(S,(Q,z,co)) in enumerate(zip(c['sets'],canonQ(c))):
        Dc.append(cnt(n,G,S,z,co,unit=True))
        Dr.append(cnt(n,G,S,[0 if v in S else 1 for v in range(n)]))
    return Dc,Dr
def bmatch(Ds,demand,cap):
    slots=[(i,k) for i in range(len(Ds)) for k in range(demand[i])]; own={}  # own[g]=list of slots
    def aug(slot,seen):
        for g in Ds[slot[0]]:
            if g in seen: continue
            if any(sl[0]==slot[0] for sl in own.get(g,[])): continue  # one unit per (system,gate)
            seen.add(g); L=own.setdefault(g,[])
            if len(L)<cap: L.append(slot); return True
            for j,o in enumerate(L):
                if aug(o,seen): L[j]=slot; return True
        return False
    return sum(1 for sl in slots if aug(sl,set()))
def twoworld(c,Dc=None,Dr=None):
    if Dc is None: Dc,Dr=worlds(c)
    dem=[len(s)-1 for s in c['sets']]
    got=bmatch(Dc+Dr,dem+dem,2); return got==2*sum(dem), got, 2*sum(dem)
def unionhall(c,Dc,Dr):
    dem=[len(s)-1 for s in c['sets']]
    U=[sorted(set(a)|set(b)) for a,b in zip(Dc,Dr)]
    return bmatch(U,dem,1)==sum(dem)
def load(f):
    if f.endswith('.json'): return [norm(json.load(open(f)))]
    return [norm(json.loads(l)) for l in open(f) if l.strip()]
