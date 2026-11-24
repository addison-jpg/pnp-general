from cxrb import *
sys.path.insert(0,S+'w8'); from verify import verify
def ess(k):
    c=cxrb(k); n0=c['n']; n=n0+3; G=[]
    # shift wires: inputs < n0 stay; gates shift by 3
    sh=lambda w: w if w<n0 else w+3
    for g in c['gates']: G.append([g[0]]+[sh(x) for x in g[1:]])
    h=[g[1] for g in G if g[0]=='not'][0]; N=n+[i for i,g in enumerate(G) if g[0]=='not'][0]
    G.append(['or',n0,n0+1]); G.append(['or',n+len(G)-1,n0+2]); t=n+len(G)-1
    G.append(['or',t,N]); a=n+len(G)-1; G.append(['or',t,h]); b=n+len(G)-1; G.append(['and',a,b]); o=n+len(G)-1
    return dict(n=n,sets=c['sets']+[[n0,n0+1,n0+2]],gates=G,outs=[sh(x) for x in c['outs']]+[o])
if __name__=='__main__':
    k=int(sys.argv[1]); c=ess(k); print(verify(c)) if c['n']<=16 else None
    pb.PS=[0.5]; print(k,[round(x,4) for x in pb.run('',c,free=True)])
    json.dump(c,open('cxU%d.json'%k,'w'))
