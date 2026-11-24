from cls2 import *
import collections
A=allcirc()
st=collections.Counter(); ex=collections.defaultdict(list)
for nm,c in A:
    T=TT(c); sets=c['sets']; m=len(sets)
    C=classes2(T)
    light=[u for u in range(T.n) if not (T.h>>(1<<u))&1]
    for i,S in enumerate(sets):
        d=len(S)-1
        if d<2: continue
        r=len(C['Dr'][i]|C['Pr'][i]); w0=len(C['D0'][i]|C['P0'][i]); w1=len(C['D1'][i]|C['P1'][i]); w1d=len(C['D1'][i])
        nl=sum(u in light for u in S)
        key=('d',d,'hard',C['hard'][i],'r>=d',r>=d,'w0>=d',w0>=d,'D1>=d',w1d>=d, 'nlight',nl)
        st[key]+=1; ex[key].append(nm)
for k,v in sorted(st.items()): print(v,k,ex[k][:3])
