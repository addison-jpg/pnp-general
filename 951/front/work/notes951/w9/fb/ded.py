# function-level private classes for each set: D_w = gates g<=OR(S_w) with >=2 units of S_w (all in cnt_0(w), pairwise disjoint over w)
# A_w = gates g>=OR(S_w), non-constant (above-gates). Reports sizes vs d_w.
import sys, json, itertools
from top2 import ev
for f in sys.argv[1:]:
    c=json.load(open(f)); n,G,sets,outs=c['n'],c['gates'],c['sets'],c['outs']
    X=list(itertools.product([0,1],repeat=n)); W=[ev(n,G,x) for x in X]
    unit=[ev(n,G,[int(v==u) for v in range(n)]) for u in range(n)]
    print(f.split('/')[-1],'s',len(G))
    for i,S in enumerate(sets):
        orS=[int(any(x[v] for v in S)) for x in X]
        D=[g for g in range(n,n+len(G)) if all(W[k][g]<=orS[k] for k in range(len(X))) and sum(unit[u][g] for u in S)>=2]
        A=[g for g in range(n,n+len(G)) if all(W[k][g]>=orS[k] for k in range(len(X))) and any(W[k][g]==0 for k in range(len(X))) and g!=outs[i]]
        print('  set',S,'d',len(S)-1,'top',G[outs[i]-n],'D_w',D,'above',A)
