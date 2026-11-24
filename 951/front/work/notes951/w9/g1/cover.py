# coverage checker: which systems are PROVED (s>=base) by: small3 (all |S|<=3), R0 (point in <=1 set of size>=3), and the
# bottom/peeling lemma G1.4 applied to a counterexample of minimal s whose point-deletions are all covered.
import itertools, sys
from functools import lru_cache
def norm(sets):
    sets=[frozenset(S) for S in sets if len(S)>=2]
    return frozenset(sets)
def degs(sets):
    d={}
    for S in sets:
        for v in S: d[v]=d.get(v,0)+1
    return d
def delete(sets,v): return norm([S-{v} for S in sets])
def feasible(sets,verbose=False):
    """is some scenario (sigma,B) consistent with G1.4?  returns list of feasible scenarios"""
    d=degs(sets); pts=sorted(d); out=[]
    for sigma in range(1,min(d.values())):
        cand=[v for v in pts if d[v]>=2+sigma]
        for r in range(2,len(cand)+1):
            for B in itertools.combinations(cand,r):
                placed=set(B); Bs=set(B); ch=True
                while ch:
                    ch=False
                    for v in pts:
                        if v in placed: continue
                        ok=True
                        if RULE4 and sigma==1 and d[v]==2:
                            Ts=[(S&placed)-{v} for S in sets if v in S]
                            tight=lambda u: (u in Bs and d[u]==3) or (u not in Bs and d[u]==2)
                            tp=[len(T)==2 and all(tight(u) for u in T) for T in Ts]
                            if all(tp) or any(t and any(u not in Bs for u in T) for t,T in zip(tp,Ts)): ok=False
                        for S in sets:
                            if not ok: break
                            if v not in S: continue
                            T=(S&placed)-{v}
                            if len(T)>=2: continue
                            if len(T)==1:
                                u=next(iter(T))
                                if (u in Bs and d[u]>=3+sigma) or (u not in Bs and d[u]>=2+sigma): continue
                            ok=False; break
                        if ok: placed.add(v); ch=True
                if len(placed)==len(pts):
                    out.append((sigma,B))
                    if not verbose: return out
    return out
memo={}
RULE4=True
def covered(sets):
    sets=norm(sets)
    if sets in memo: return memo[sets]
    if all(len(S)<=3 for S in sets): memo[sets]=True; return True
    d=degs(sets)
    for v in d:
        if sum(1 for S in sets if v in S and len(S)>=3)<=1:
            r=covered(delete(sets,v)); memo[sets]=r; return r
    r=all(covered(delete(sets,v)) for v in d) and not feasible(sets)
    memo[sets]=r; return r
if __name__=='__main__':
    core8=[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7]]
    grid=[[4*i+j for i in range(3)] for j in range(4)]+[[4*i+j for j in range(4)] for i in range(3)]
    grid44=[[4*i+j for i in range(4)] for j in range(4)]+[[4*i+j for j in range(4)] for i in range(4)]
    for nm,s in [('core8',core8),('grid4x3',grid),('grid4x4',grid44)]:
        print(nm,'covered:',covered(s),'feasible scenarios:',feasible(norm(s),True)[:5])
