import json, sys, itertools
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/chk')
import chargeok_check as K, conedbl as C
from collections import Counter
def merges(n,G,cone,zv,unit,S):
    # union-find on S over cone gates in index order; returns list of merge gates
    par={u:u for u in S}
    def f(u):
        while par[u]!=u: u=par[u]
        return u
    B=lambda i:[u for u in S if unit[u][i]]
    M=[]
    for i in sorted(cone):
        g=G[i-n]
        if zv[i]!=0 or g[0]!='or': continue
        a,b=g[1],g[2]
        Ba=[u for u in B(a) if zv[a]==0] if True else []
        ra={f(u) for u in B(a)}; rb={f(u) for u in B(b)}
        assert len(ra)<=1 and len(rb)<=1, (i,ra,rb)
        if ra and rb and ra!=rb:
            par[ra.pop()]=rb.pop(); M.append(i)
    roots={f(u) for u in S}
    assert len(roots)==1
    return M
def run(files,verbose=0):
    H=Counter(); worst=[]
    for fn in files:
      for l in open(fn):
        c=C.norm(json.loads(l)); n,S,G,outs=c['n'],[set(x) for x in c['sets']],c['gates'],c['outs']
        s=len(G); nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=G[nw-n][1]
        ev=lambda x:K.evaluate(n,G,x)
        unit=[ev([int(v==u) for v in range(n)]) for u in range(n)]
        if all(unit[u][nw]==0 for u in range(n)): H['du']+=1; continue
        cones=[K.cone(n,G,o) for o in outs]
        z=lambda Q: ev([0 if v in Q else 1 for v in range(n)])
        hardN=[i for i in range(len(S)) if nw in cones[i] and z(S[i])[h]==1]
        if len(hardN)<2: H['<2hard']+=1; continue
        # choose Q: for hardN minimal-D hitting sets (as conedbl), else S
        sl,dbl,info=C.analyse(c)
        Ms=[]; 
        for i in range(len(S)):
            Q=set(info[i][1][0]); zv=z(Q)
            Ms.append(merges(n,G,cones[i],zv,unit,S[i]))
        mult=Counter(g for M in Ms for g in M)
        exc=sum(v-1 for v in mult.values() if v>1)
        nand=sum(1 for g in G if g[0]=='and')
        unch=s-len(mult)
        H['circ']+=1; H['exc%d'%exc]+=1
        assert s>=sum(len(x)-1 for x in S)+1+nand-exc
        if exc>nand: H['exc>nand']+=1; worst.append((exc,nand,c))
        if exc>=1 and verbose and H['shown']<verbose:
            H['shown']+=1; print(c,'\n mult',{g:v for g,v in mult.items() if v>1},'nand',nand,'hard',hardN,[info[i] for i in hardN])
    print(dict(H))
    for w in worst[:3]: print(w)
if __name__=='__main__': run(sys.argv[2:],int(sys.argv[1]))
