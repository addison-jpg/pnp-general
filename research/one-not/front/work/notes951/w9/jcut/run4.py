from cls2 import *
import collections,sys
A=allcirc()
stat=collections.Counter(); fails=collections.defaultdict(list)
combos=[['Dr','Pr','D0','P0','D1'],['Dr','Pr','D0','P0','D1','P1'],['Dr','Pr','D0','D1','P1'],['Dr','Pr','P0','D1','P1'],['Dr','D0','P0','D1','P1'],['Pr','D0','P0','D1','P1'],['D0','P0','D1','P1','Pr']]
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets); dem=[len(S)-1 for S in sets]; base=sum(dem)
    C=classes2(T)
    for combo in combos:
        adj=[set().union(*[C[k][i] for k in combo]) for i in range(m)]
        if maxflow_match(dem,adj)<base: stat['+'.join(combo)]+=1; fails['+'.join(combo)].append(nm)
print(stat)
for k,v in fails.items(): print(k,v[:8])
