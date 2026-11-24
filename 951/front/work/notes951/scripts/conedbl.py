# Cone-restricted D with Lean's masked Good: for a set whose output cone does not contain the NOT,
# the NOT is masked to a constant, so every Q is Good; otherwise Good = h(z_Q)=0 or NOT false at all units.
import json, itertools, sys, chargeok_check as K
from collections import Counter
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def analyse(c):
    n,S,G,outs=c['n'],[set(x) for x in c['sets']],c['gates'],c['outs']; s=len(G)
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    ev=lambda x: K.evaluate(n,G,x)
    unit=[ev([int(v==u) for v in range(n)]) for u in range(n)]
    du=all(unit[u][nw]==0 for u in range(n))
    cones=[K.cone(n,G,o) for o in outs]; mult=Counter(); tot=0; info=[]
    for wi,R in enumerate(S):
        best=None
        for r in range(n+1):
            for ex in itertools.combinations([v for v in range(n) if v not in R],r):
                Q=R|set(ex); z=ev([0 if v in Q else 1 for v in range(n)])
                if nw in cones[wi] and not (z[nw]==1 or du): continue
                d=[i for i in sorted(cones[wi]) if z[i]==0 and sum(unit[u][i] for u in R)>=2]
                if best is None or len(d)<len(best[1]): best=(sorted(Q),d)
        tot+=len(best[1]); mult.update(best[1]); info.append((sorted(R),best, nw in cones[wi]))
    return s-tot, {k:v for k,v in mult.items() if v>1}, info
if __name__=='__main__':
    H=Counter(); ex=[]; minsl_dbl=99
    for f in sys.argv[1:]:
        for l in open(f):
            c=norm(json.loads(l)); sl,dbl,info=analyse(c); H['n']+=1; H['viol']+=sl<0
            if dbl:
                H['with_double']+=1; minsl_dbl=min(minsl_dbl,sl)
                if len(ex)<2 or sl<=1: ex.append((sl,c,dbl,info))
    print(dict(H),'min slack among circuits with doubles',minsl_dbl)
    ex.sort(key=lambda t:t[0])
    for sl,c,dbl,info in ex[:2]:
        print('slack',sl,'s',len(c['gates']),'doubles',dbl); print('  gates',c['gates'],'outs',c['outs'])
        for R,b,isN in info: print('   set',R,'Nset' if isN else '','Q',b[0],'D',b[1])
