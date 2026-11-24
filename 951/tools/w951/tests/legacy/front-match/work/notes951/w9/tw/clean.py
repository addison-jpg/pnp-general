import itertools, json, sys
sys.path.insert(0,'.')
from tw import ev
def tables(c):
    n,G=c['n'],c['gates']; X=list(itertools.product([0,1],repeat=n))
    W=[ev(n,G,x) for x in X]; return [tuple(w[i] for w in W) for i in range(n+len(G))]
def cleanup(c):
    while True:
        n,G,outs=c['n'],c['gates'],c['outs']; tt=tables(c); first={}; rep={}
        for i,t in enumerate(tt):
            if t in first and i>=n: rep[i]=first[t]
            else: first.setdefault(t,i)
        # remove unread
        read=set(j for gt in G for j in gt[1:3] if j is not None)|set(outs)
        dead={n+k for k in range(len(G)) if n+k not in read}
        if not rep and not dead: return c
        drop=set(rep)|dead
        def R(j):
            while j in rep: j=rep[j]
            return j
        newidx={}; NG=[]
        for k,gt in enumerate(G):
            i=n+k
            if i in drop: continue
            newidx[i]=n+len(NG)
            args=[R(j) for j in gt[1:] if j is not None]
            args=[j if j<n else newidx[j] for j in args]
            NG.append([gt[0]]+args)
        outs=[R(o) for o in outs]; outs=[o if o<n else newidx[o] for o in outs]
        c=dict(n=n,sets=c['sets'],gates=NG,outs=outs)
