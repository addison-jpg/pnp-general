from cls2 import *
import collections
A=allcirc()
NAMES=['Dr','Pr','D0','P0','D1']
stat=collections.Counter(); kinds=collections.Counter(); ex={}
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets); dem=[len(S)-1 for S in sets]
    C=classes2(T)
    U=[set().union(*[C[k][i] for k in NAMES]) for i in range(m)]
    for i in range(m):
        stat['sets']+=1
        if len(U[i])<dem[i]: stat['short']+=1; ex.setdefault('short',[]).append((nm,i))
        for k in NAMES:
            if len(C[k][i])>=dem[i]: stat['alone_'+k]+=1
        for j in range(m):
            if i<j and U[i]&U[j]:
                stat['confpairs']+=1
                for g in U[i]&U[j]:
                    for x in [k for k in NAMES if g in C[k][i]]:
                        for y in [k for k in NAMES if g in C[k][j]]:
                            kinds[(x,y)]+=1; ex.setdefault((x,y),(nm,i,j,g))
print(stat); print(kinds); print(ex)
