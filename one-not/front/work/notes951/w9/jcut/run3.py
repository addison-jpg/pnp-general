from cls2 import *
import collections
A=allcirc()
stat=collections.Counter(); kinds=collections.Counter(); ex={}
NAMES=['Dr','Pr','D0','P0','D1','P1']
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets); dem=[len(S)-1 for S in sets]; base=sum(dem)
    C=classes2(T)
    U=[set().union(*[C[k][i] for k in NAMES]) for i in range(m)]
    for combo in (['Dr','Pr'],['Dr','Pr','D0','P0'],['Dr','Pr','D1','P1'],NAMES,['D0','P0','D1','P1']):
        adj=[set().union(*[C[k][i] for k in combo]) for i in range(m)]
        if maxflow_match(dem,adj)<base: stat['+'.join(combo)]+=1
    stat['n']+=1
    for i in range(m):
        if len(U[i])<dem[i]: stat['short']+=1
        for j in range(m):
            if i==j: continue
            for g in U[i]&U[j]:
                a=tuple(k for k in NAMES if g in C[k][i]); b=tuple(k for k in NAMES if g in C[k][j])
                for x in a:
                    for y in b:
                        kinds[(x,y)]+=1; ex.setdefault((x,y),(nm,i,j,g))
print(stat)
for k,v in sorted(kinds.items(),key=lambda t:-t[1]): print(k,v,ex[k])
