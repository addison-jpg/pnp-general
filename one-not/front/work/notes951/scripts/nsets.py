# For each circuit: N-sets = sets whose output cone contains the NOT gate; hard = h(z_S) = 1.
# Count circuits with >= 2 hard N-sets, and whether Theorem X's pair condition can be met among them
# (choose for each hard N-set a minimal Q ⊇ S with h(z_Q)=0; need pairwise |S_a∩Q_b|<=1 or |S_b∩Q_a|<=1).
import json, itertools, sys, chargeok_check as K
from collections import Counter
def analyse(c):
    n,S,G,outs=c['n'],[set(x) for x in c['sets']],c['gates'],c['outs']
    p=[k for k,g in enumerate(G) if g[0]=='not'][0]; nw=n+p; hw=G[p][1]
    ev=lambda x: K.evaluate(n,G,x)
    h=lambda Q: ev([0 if v in Q else 1 for v in range(n)])[hw]
    if ev([0]*n)[hw]==1: return 'h0=1',None
    cones=[K.cone(n,G,o) for o in outs]
    hardN=[i for i,R in enumerate(S) if nw in cones[i] and h(R)==1]
    if len(hardN)<2: return 'le1',len(hardN)
    # minimal Q choices per hard N-set
    choices=[]
    for i in hardN:
        rest=[v for v in range(n) if v not in S[i]]; mins=[]
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=S[i]|set(ex)
                if h(Q)==0 and not any(m<=Q for m in mins): mins.append(Q)
        choices.append(mins)
    for combo in itertools.product(*choices):
        ok=all(len(S[a]&combo[jb])<=1 or len(S[b]&combo[ja])<=1
               for ja,a in enumerate(hardN) for jb,b in enumerate(hardN) if ja<jb)
        if ok: return 'pairOK',len(hardN)
    return 'BAD',len(hardN)
H=Counter(); ex=[]
for f in sys.argv[1:]:
    for l in open(f):
        c=json.loads(l)
        if 'gates' in c and c['gates'] and isinstance(c['gates'][0],list) and len(c['gates'][0])==3 and c['gates'][0][0]!='not':
            c['gates']=[['not',g[1]] if g[0]=='not' else g for g in c['gates']]
        r,k=analyse(c); H[r]+=1
        if r=='BAD' and len(ex)<3: ex.append(c)
print(dict(H))
for c in ex: print('BAD example', json.dumps(c))
