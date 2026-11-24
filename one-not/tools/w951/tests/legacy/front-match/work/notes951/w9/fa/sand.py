# Sandwich classes (system-free): L_a = gates g<=o_a pointwise, true on >=2 units of S_a; U_a = gates g>=o_a pointwise, g(z_{S_a})=0.
import sys; sys.path.insert(0,'.')
from lib import *
from sig import files
from collections import Counter
def tts(c):
    n,G=c['n'],c['gates']; full=(1<<(1<<n))-1
    w=[]
    for v in range(n):
        m=0
        for x in range(1<<n):
            if (x>>v)&1: m|=1<<x
        w.append(m)
    for g in G:
        if g[0]=='not': w.append(full&~w[g[1]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w,full
def classes(c):
    n=c['n']; w,full=tts(c); res=[]
    for S,o in zip(c['sets'],c['outs']):
        f=0
        for u in S: f|=w[u]
        assert w[o]==f
        zS=sum(1<<v for v in range(n) if v not in S)
        L=[i for i in range(n,len(w)) if w[i]&~f==0 and sum((w[i]>>(1<<u))&1 for u in S)>=2]
        U=[i for i in range(n,len(w)) if f&~w[i]==0 and not (w[i]>>zS)&1]
        res.append((set(L),set(U)))
    return res
if __name__=='__main__':
    H=Counter()
    for f in files+sys.argv[1:]:
        try: cs=load(f)
        except Exception: continue
        for c in cs:
            if c['n']>12: continue
            R=classes(c); P=[l|u for l,u in R]; H['circ']+=1
            if sum(map(len,P))!=len(set().union(*P)): H['NOT DISJOINT']+=1
            for S,p,o in zip(c['sets'],P,c['outs']):
                d=len(S)-1; k=(len(S),c['gates'][o-c['n']][0])
                H[('set size,outop',k)]+=1
                if len(p)<min(d,2): H['VIOL min(d,2)']+=1
                if len(p)<d: H[('short',k)]+=1
            if any(len(S)>=4 for S in c['sets']): print(f.split('/')[-1],[(len(S),c['gates'][o-c['n']][0],sorted(l),sorted(u)) for S,(l,u),o in zip(c['sets'],R,c['outs'])])
    for k,v in sorted(H.items(),key=str): print(k,v)
