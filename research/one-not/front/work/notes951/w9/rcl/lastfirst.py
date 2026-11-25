# 2.3 proof wording: "the LAST wire on the walk that vanishes" vs reachability "through wires vanishing on Z"
import random, collections
from rl import *
from t2 import configs
rng=random.Random(3); st=collections.Counter(); ex=None
for name,c in files():
    if c['n']>10: continue
    Lc=L(c)
    if not(Lc.ok and Lc.correct and not Lc.h0): continue
    W=Lc.W
    cf=[(k,)+x for k in range(len(Lc.S)) for x in configs(Lc,k,rng,2)]
    for _ in range(6):
        if len(cf)<2: break
        (ka,ta,Za,ata),(kb,tb,Zb,atb)=rng.sample(cf,2)
        if ka==kb: continue
        Z=Za|Zb; van=lambda w:(W[w]&Z)==0
        for g in Lc.gatew:
            if not van(g): continue
            for al in list(ata.values())+list(atb.values()):
                if not (W[g]>>al)&1: continue
                if any(van(i) and (W[i]>>al)&1 for i in Lc.inputs): continue
                for _ in range(3):
                    walk=[g]; w=g
                    while w>=Lc.n and w!=Lc.yw:
                        cs=[x for x in Lc.ch(w) if (W[x]>>al)&1]; w=rng.choice(cs); walk.append(w)
                    assert not van(walk[-1])
                    vs=[i for i,x in enumerate(walk) if van(x)]
                    last=vs[-1]; first=next(i for i,x in enumerate(walk) if not van(x))-1
                    st['walks']+=1
                    for idx,nm in ((last,'last'),(first,'first')):
                        G=walk[idx]; assert Lc.op(G)=='and' and van(G) and (W[G]>>al)&1 and not van(walk[idx+1])
                    assert all(van(x) for x in walk[:first+1])
                    if last!=first:
                        st['last!=first']+=1
                        # is 'last' reachable from g through vanishing wires at all (any path)?
                        seen=set(); s2=[g]
                        while s2:
                            x=s2.pop()
                            if x in seen: continue
                            seen.add(x)
                            if x>=Lc.n and x!=Lc.yw: s2+=[y for y in Lc.ch(x) if van(y)]
                        if walk[last] not in seen:
                            st['last NOT reachable via vanishing wires']+=1; ex=ex or (name,g,al,walk)
print(dict(st),ex)
