from cls3 import *
import collections
A=allcirc(); st=collections.Counter(); bad=[]
for nm,c in A:
    T=TT(c); m=len(c['sets'])
    hard=[T.o[i]|T.U0!=T.FULL for i in range(m)]
    for i in range(m):
        b=0 if hard[i] else 1
        r=explore(T,i,b)
        if r is None: st['RMfail',b]+=1; bad.append((nm,i,b)); continue
        ors,L=r
        st['ok',b,len(ors)>=L-1]+=1
        if len(ors)<L-1: bad.append((nm,i,b))
print(st,bad[:10])
