from cxU import *
def ess3(k,r):
    c=cxrb(k); n0=c['n']; n=n0+r; G=[]
    sh=lambda w: w if w<n0 else w+r
    for g in c['gates']: G.append([g[0]]+[sh(x) for x in g[1:]])
    h=[g[1] for g in G if g[0]=='not'][0]; N=n+[i for i,g in enumerate(G) if g[0]=='not'][0]
    D=list(range(n0,n0+r))
    t1=chain(G,n,D[:-1]); t2=chain(G,n,D[1:])
    G.append(['or',t1,N]); G.append(['or',n+len(G)-1,D[-1]]); a=n+len(G)-1
    G.append(['or',t2,h]); G.append(['or',n+len(G)-1,D[0]]); b=n+len(G)-1; G.append(['and',a,b]); o=n+len(G)-1
    return dict(n=n,sets=c['sets']+[D],gates=G,outs=[sh(x) for x in c['outs']]+[o])
if __name__=='__main__':
    k,r=int(sys.argv[1]),int(sys.argv[2]); c=ess3(k,r); json.dump(c,open('cxU_%d_%d.json'%(k,r),'w'))
    if c['n']<=16: print(verify(c))
    print(k,r,c['n'],len(c['gates']),sum(len(s)-1 for s in c['sets']),'L_AB(1/2) =',lower(c),flush=True)
