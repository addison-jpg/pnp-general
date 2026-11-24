from cls4 import *
import collections
A=allcirc(); st=collections.Counter(); rows=[]
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets); dem=[len(S)-1 for S in sets]; base=sum(dem)
    C=allcls(T); hard=C['hard']
    adj=[ (C['D1e'][i]|C['D0p'][i]|C['Dr'][i]|C['Pr'][i]) for i in range(m)]
    d=base-maxflow_match(dem,adj)
    used=set().union(*adj)
    nd=[g for g in range(T.n,T.W) if g not in used and T.w[0][g]!=T.w[1][g] and g!=T.Ni]
    st['n']+=1; st['d>0']+=d>0; st['d<=nd(noN)']+=d<=len(nd); st['d<=nd+1']+=d<=len(nd)+1
    if d>0: rows.append((nm,d,len(nd),len(c['gates'])-base))
print(st); print(rows)
