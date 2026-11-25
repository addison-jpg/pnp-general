from cxrb import *
sys.path.insert(0,S+'w8'); from verify import verify
def ess2(k):
    c=cxrb(k); n0=c['n']; n=n0+2; G=[]
    sh=lambda w: w if w<n0 else w+2
    for g in c['gates']: G.append([g[0]]+[sh(x) for x in g[1:]])
    h=[g[1] for g in G if g[0]=='not'][0]; N=n+[i for i,g in enumerate(G) if g[0]=='not'][0]
    p,q=n0,n0+1
    G.append(['or',q,N]); G.append(['or',p,n+len(G)-1]); a=n+len(G)-1
    G.append(['or',p,h]); G.append(['or',q,n+len(G)-1]); b=n+len(G)-1; G.append(['and',a,b]); o=n+len(G)-1
    return dict(n=n,sets=c['sets']+[[p,q]],gates=G,outs=[sh(x) for x in c['outs']]+[o])
def lower(c,sets=(0,1),p=0.5):
    T=TT(c); assert T.correct()
    n=T.n; W=T.w['real']; gates=range(n,T.W); ents=[]; dem=[len(s)-1 for s in c['sets']]
    for wi in sets:
        R=c['sets'][wi]; rest=[v for v in range(n) if v not in R]; agg=collections.Counter()
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                cl=frozenset(g for g in gates if not (W[g]>>z)&1 and sum((W[g]>>(z|1<<u))&1 for u in R)>=2)
                agg[cl]+=(p**r)*((1-p)**(len(rest)-r))
        # NOTE: merging equal classes is exact for the sub-selection LP (same class => same constraints, convexity)
        for cl,lam in agg.items(): ents.append((wi,cl,lam))
    return maxload(dem,ents)
if __name__=='__main__':
    k=int(sys.argv[1]); c=ess2(k); json.dump(c,open('cxU%d.json'%k,'w'))
    if c['n']<=14: print(verify(c))
    print(k,c['n'],len(c['gates']),'L_AB(1/2) =',lower(c))
