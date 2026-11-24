import sys, json, itertools
sys.path.insert(0,'../../w8')
from verify import verify
from top2 import ev
from collections import Counter
def t3(c):
    n,G,sets,outs=c['n'],c['gates'],c['sets'],c['outs']
    X=list(itertools.product([0,1],repeat=n)); W=[ev(n,G,x) for x in X]; idx={x:k for k,x in enumerate(X)}
    gates=range(n,n+len(G)); orS=[[int(any(x[v] for v in S)) for x in X] for S in sets]
    unit=[W[idx[tuple(int(v==u) for v in range(n))]] for u in range(n)]
    le=lambda g,i: all(W[k][g]<=orS[i][k] for k in range(len(X)))
    ge=lambda g,i: all(W[k][g]>=orS[i][k] for k in range(len(X)))
    D=[];P=[]
    GE=[[ge(g,i) for i in range(len(sets))] for g in gates]
    for i,S in enumerate(sets):
        D.append({g for g in gates if sum(unit[u][g] for u in S)>=2 and le(g,i)})
        P.append({g for g in gates if GE[g-n][i] and sum(GE[g-n])==1 and any(W[k][g]==0 for k in range(len(X)))})
    Pi=[D[i]|P[i] for i in range(len(sets))]
    disj=sum(map(len,Pi))==len(set().union(*Pi))
    m=[]
    for i,S in enumerate(sets):
        best=0; rest=[v for v in range(n) if v not in S]
        for zm in itertools.product([0,1],repeat=len(rest)):
            z=[0]*n
            for v,b in zip(rest,zm): z[v]=b
            wz=W[idx[tuple(z)]]; at=[]
            for u in S:
                p=list(z); p[u]=1; at.append(W[idx[tuple(p)]])
            best=max(best,sum(1 for g in Pi[i] if wz[g]==0 and sum(a[g] for a in at)>=2))
        m.append(best)
    return disj,m
for f in sys.argv[1:]:
    cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    H=Counter()
    for c in cs:
        if not any(len(s)>=3 for s in c['sets']): continue
        c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]
        if not verify(c)['clean']: continue
        disj,m=t3(c); H['n']+=1; H['disjoint']+=disj
        H['m>=min(d,2) all']+=all(mi>=min(len(s)-1,2) for mi,s in zip(m,c['sets']))
        H['m>=d all']+=all(mi>=len(s)-1 for mi,s in zip(m,c['sets']))
        if len(cs)==1: print('  m',m,'d',[len(s)-1 for s in c['sets']])
    print(f.split('/')[-1],dict(H))
