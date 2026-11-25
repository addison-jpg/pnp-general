from cxU2 import *
def lower_fast(c,sets=(0,1),p=0.5):
    T=TT(c); assert T.correct()
    n=T.n; W=T.w['real']; gates=range(n,T.W); ents=[]; dem=[len(s)-1 for s in c['sets']]
    nb=(1<<n)//8; tb={g:W[g].to_bytes(nb,'little') for g in gates}
    bit=lambda g,z: (tb[g][z>>3]>>(z&7))&1
    for wi in sets:
        R=c['sets'][wi]; rest=[v for v in range(n) if v not in R]; agg=collections.Counter()
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                cl=frozenset(g for g in gates if not bit(g,z) and sum(bit(g,z|1<<u) for u in R)>=2)
                assert len(cl)>=len(R)-1
                agg[cl]+=(p**r)*((1-p)**(len(rest)-r))
        for cl,lam in agg.items(): ents.append((wi,cl,lam))
    ess=all(T.w[0][o]!=t for o,t in zip(c['outs'],T.o)) or any(T.w[0][o]!=t for o,t in zip(c['outs'],T.o))
    c0w=any(T.w[0][o]!=t for o,t in zip(c['outs'],T.o)); c1w=any(T.w[1][o]!=t for o,t in zip(c['outs'],T.o))
    tabs=W; clean=len(set(tabs))==len(tabs) and all(0<t<T.FULL for t in tabs)
    read=set(j for g in c['gates'] for j in g[1:])|set(c['outs'])
    return maxload(dem,ents),dict(correct=True,C0wrong=c0w,C1wrong=c1w,clean=clean,read=all(n+i in read for i in range(len(c['gates']))))
if __name__=='__main__':
    k,r=int(sys.argv[1]),int(sys.argv[2]); c=ess3(k,r); json.dump(c,open('cxU_%d_%d.json'%(k,r),'w'))
    print(k,r,c['n'],len(c['gates']),sum(len(s)-1 for s in c['sets']),'L_AB(1/2), flags =',lower_fast(c),flush=True)
