from cls4 import *
import collections
A=allcirc(); st=collections.Counter(); worst=[]
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets); dem=[len(S)-1 for S in sets]; base=sum(dem); s=len(c['gates'])
    C=allcls(T); hard=C['hard']
    light=lambda u: not (T.h>>(1<<u))&1
    adj=[ (C['D1e'][i] if not hard[i] else C['D0p'][i]) for i in range(m)]
    mt=maxflow_match(dem,adj)
    dA=base-mt
    def1=sum(sum(not light(u) for u in S) for i,S in enumerate(sets) if not hard[i] and sum(light(u) for u in S)>=1)
    def1=sum(min(len(S)-1,sum(not light(u) for u in S)) for i,S in enumerate(sets) if not hard[i])
    # world-0 deficiency among hard sets alone
    hi=[i for i in range(m) if hard[i]]
    def0=sum(dem[i] for i in hi)-maxflow_match([dem[i] for i in hi],[C['D0p'][i] for i in hi])
    used=set().union(*adj)
    out=[g for g in range(T.n,T.W) if g not in used]
    ndep=[g for g in out if T.w[0][g]!=T.w[1][g]]
    st['n']+=1
    st['dA>0']+=dA>0; st['def0>0']+=def0>0; st['def1>0']+=def1>0
    st['dA<=#out']+= dA<=len(out); st['dA<=#Ndep_out']+= dA<=len(ndep)
    st['def0<=#Ndep_out']+= def0<=len(ndep)
    st['dA<=1']+=dA<=1
    worst.append((dA,def0,def1,len(ndep),len(out),s-base,nm))
print(st)
worst.sort(reverse=True)
for x in worst[:15]: print(x)
print([x for x in worst if x[1]>0][:15])
