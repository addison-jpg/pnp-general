import sys,itertools
from star import load,tts
from collections import Counter
def cls(c):
    n=c['n'];var,w,full=tts(c)
    hi=[g[1] for g in c['gates'] if g[0]=='not'];
    h=w[hi[0]] if hi else 0
    sets=[S for S in c['sets'] if len(S)>=2];A=[]
    for S in sets:
        a=0
        for u in S:a|=var[u]
        A.append(a)
    C=Counter()
    for k in range(n,len(w)):
        g=w[k];L=U=False
        for a,b in itertools.combinations(range(len(A)),2):
            if g&~(A[a]&A[b])&full==0:L=True
            if (A[a]|A[b])&~g==0:U=True
        if L: C['L:'+('<=N' if g&h==0 else '<=h' if g&~h&full==0 else 'mixed')]+=1
        if U: C['U:'+('>=N' if (full^h)&~g==0 else '>=h' if h&~g==0 else 'mixed')]+=1
    return C
for f in sys.argv[1:]:
    T=Counter()
    for c in load(f): T+=cls(c)
    print(f.split('scratchpad/')[-1],dict(T))
