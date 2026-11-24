from plib import *
import collections
A=alldata(); st=collections.Counter(); bad=[]
for nm,c in A:
    T=C(c)
    if not T.correct(): st['incorrect']+=1; continue
    K=T.classes(); st['circ']+=1
    for i in range(T.m):
        st['sets']+=1
        if not T.hard[i]:
            st['easy']+=1
            if len(K['Dr'][i])<T.d[i]: st['easy_Dr_short']+=1; bad.append((nm,i))
            if len(K['DrS'][i])<T.d[i]: st['easy_DrS_short']+=1
            if not K['D1'][i]<=K['Dr'][i]: st['easy_D1_notin_Dr']+=1
        else:
            st['hard']+=1
            if len(pistar(K,i))<T.d[i]: st['hard_short']+=1
            if len(K['Dr'][i]|K['Pr'][i])<T.d[i]: st['hard_T3_short']+=1
    for nmset in (('Dr','Pr','D0','P0','D1'),('DrS','Pr','D0','P0','D1')):
        U=[pistar(K,i,nmset) for i in range(T.m)]
        if match(T.d,U)<T.base: st['matchfail'+nmset[0]]+=1
        for i in range(T.m):
            for j in range(i):
                if U[i]&U[j]: st['conf'+nmset[0]]+=1; bad.append((nm,i,j,U[i]&U[j]))
print(st); print(bad[:10])
