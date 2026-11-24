# Enumerate ALL Lean test systems (z, fat atoms, K) for each set; keep inclusion-maximal counted sets; test MatchG.
import sys, json, itertools
from verify import evalN
def menus(c, coneonly=False):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; ng=len(G)
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    down={nw}
    for k,g in enumerate(G):
        if any(j in down for j in g[1:]): down.add(n+k)
    def cone(o):
        seen=set(); st=[o]
        while st:
            i=st.pop()
            if i in seen or i<n: continue
            seen.add(i); st+=G[i-n][1:]
        return seen
    res=[]
    for wi,R in enumerate(S):
        cn=cone(outs[wi]); cands={}
        rest=[v for v in range(n) if v not in R]
        for zm in itertools.product([0,1],repeat=len(rest)):
            z=[0]*n
            for v,b in zip(rest,zm): z[v]=b
            wz=evalN(n,G,z); ones=[v for v in rest if z[v]]
            # K options: with NOT (needs Good) -> all gates (or cone); without NOT (only if out not downstream)
            sig={}
            for u in R:
                d={}
                for T in itertools.chain.from_iterable(itertools.combinations(ones,r) for r in range(len(ones)+1)):
                    p=[0]*n; p[u]=1
                    for v in T: p[v]=1
                    wp=evalN(n,G,p)
                    key=(wp[nw],tuple(i for i in range(n,n+ng) if wz[i]==0 and wp[i]==1))
                    d.setdefault(key,(u,)+T)
                it=list(d.items())
                sig[u]=[a for a in it if not any(b is not a and b[0][0]<=a[0][0] and set(a[0][1])<=set(b[0][1]) and (b[0]!=a[0]) for b in it)]
            for combo in itertools.product(*[sig[u] for u in R]):
                nN=sum(k[0][0] for k in combo)
                good = wz[nw]==1 or nN<=1
                opts=[]
                if good: opts.append(cn if coneonly else set(range(n,n+ng)))
                elif outs[wi] not in down: opts.append(cn-down if coneonly else set(range(n,n+ng))-down)
                for Kset in opts:
                    cnt=frozenset(i for i in Kset if sum(i in k[0][1] for k in combo)>=2)
                    if cnt not in cands: cands[cnt]=(tuple(z),[k[1] for k in combo])
        mx=[x for x in cands if not any(x<y for y in cands)]
        res.append({x:cands[x] for x in mx})
    return res
def bmatch(Ds, demand):
    slots=[(i,k) for i in range(len(Ds)) for k in range(demand[i])]; owner={}
    def aug(slot, seen):
        for g in Ds[slot[0]]:
            if g in seen: continue
            seen.add(g)
            if g not in owner or aug(owner[g], seen): owner[g]=slot; return True
        return False
    return sum(1 for sl in slots if aug(sl,set()))
if __name__=='__main__':
    c=json.load(open(sys.argv[1])); M=menus(c, coneonly=len(sys.argv)>2)
    dem=[len(s)-1 for s in c['sets']]; base=sum(dem)
    print('menu sizes (maximal counted sets):',[len(m) for m in M])
    best=(-1,None); nfull=0; tot=0
    for combo in itertools.product(*[list(m) for m in M]):
        tot+=1; b=bmatch([sorted(x) for x in combo],dem)
        if b==base: nfull+=1
        if b>best[0]: best=(b,combo)
    print('assignments',tot,'with full matching',nfull,'best',best[0],'of base',base)
    for wi,x in enumerate(best[1]): print(' set',c['sets'][wi],'cnt',sorted(x),'z',M[wi][x][0],'atoms',M[wi][x][1])
