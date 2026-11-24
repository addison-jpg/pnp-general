# cover2: coverage checker with rules (i),(ii) + capacity (ii'), (iv-a), (v).  Sound over-approximation of "a minimal counterexample
# scenario exists"; covered(system)=True means s>=base is PROVED for the system (given small3, R0, and the lemmas of g1_fable.md).
import itertools, sys
from cover import norm, degs, delete
def feasible(sets,verbose=False,rules='245'):
    d=degs(sets); pts=sorted(d); out=[]
    Sv={v:[S for S in sets if v in S] for v in pts}
    for sigma in range(1,min(d.values())):
        cand=[v for v in pts if d[v]>=2+sigma]
        for r in range(2,len(cand)+1):
            for B in itertools.combinations(cand,r):
                Bs=frozenset(B)
                tight=lambda u: (u in Bs and d[u]==2+sigma) or (u not in Bs and d[u]==1+sigma)
                def cap1(u): return (d[u]-sigma-2) if u in Bs else (d[u]-sigma-1)   # singleton users
                seen=set()
                def status(v,placed):
                    """None if not placeable; else dict of consumption"""
                    use={}
                    Ts=[(S&placed)-{v} for S in Sv[v]]
                    for T in Ts:
                        if not T: return None
                        if len(T)==1:
                            u=next(iter(T)); use[('s',u)]=use.get(('s',u),0)+1
                    if sigma==1 and d[v]==2:
                        tp=[len(T)==2 and all(tight(u) for u in T) for T in Ts]
                        if '4' in rules:
                            if all(tp): return None
                            if any(t and any(u not in Bs for u in T) for t,T in zip(tp,Ts)): return None
                        if '5' in rules:
                            for t,T in zip(tp,Ts):
                                if t:
                                    for u in T: use[('p',u)]=use.get(('p',u),0)+1
                    return use
                def okuse(use,used):
                    for (k,u),c in use.items():
                        tot=used.get((k,u),0)+c
                        if k=='s' and tot>(cap1(u) if '2' in rules else (99 if cap1(u)>=1 else 0)): return False
                        if k=='p' and tot>1: return False
                    return True
                def dfs(placed,used):
                    # free moves greedily
                    ch=True
                    while ch:
                        ch=False
                        for v in pts:
                            if v in placed: continue
                            u=status(v,placed)
                            if u is not None and not u: placed=placed|{v}; ch=True
                    if len(placed)==len(pts): return True
                    key=(placed,tuple(sorted(used.items())))
                    if key in seen: return False
                    seen.add(key)
                    for v in pts:
                        if v in placed: continue
                        u=status(v,placed)
                        if u is None or not okuse(u,used): continue
                        nu=dict(used)
                        for k,c in u.items(): nu[k]=nu.get(k,0)+c
                        if dfs(placed|{v},nu): return True
                    return False
                if dfs(Bs,{}):
                    out.append((sigma,B))
                    if not verbose: return out
    return out
memo={}
def covered(sets,rules='245'):
    sets=norm(sets); key=(sets,rules)
    if key in memo: return memo[key]
    if all(len(S)<=3 for S in sets): memo[key]=True; return True
    d=degs(sets)
    for v in d:
        if sum(1 for S in sets if v in S and len(S)>=3)<=1:
            r=covered(delete(sets,v),rules); memo[key]=r; return r
    r=all(covered(delete(sets,v),rules) for v in d) and not feasible(sets,False,rules)
    memo[key]=r; return r
if __name__=='__main__':
    import pickle
    for n in sys.argv[1:]:
        R=pickle.load(open(f'cores{n}.pkl','rb'))
        for rules in ['','2','24','245']:
            cv=[covered(s,rules) for s in R]
            print('n',n,'skeleton cores',len(R),'rules',rules or '(i),(ii) only','covered',sum(cv),flush=True)
        k=0
        for s,c in zip(R,cv):
            if not c and all(covered(delete(norm(s),v)) for v in degs(norm(s))) and k<8:
                k+=1; print(' uncovered (deletions covered):',s,sorted(degs(norm(s)).values()),feasible(norm(s),True)[:2])
