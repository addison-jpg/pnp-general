# FUNCTION-LEVEL two-world Theorem X: depends only on (n, sets, h).
# system σ=(z, p_u): z=0 on S, p_u=e_u+T_u, T_u ⊆ ones(z); legal (Lean GoodT): h(z)=0 or #{u: h(p_u)=0} <= 1.
# sep(σ->σ'): #{u∈S : not(p_u <= z' and h(p_u) >= h(z'))} <= 1.  If sep(σ->σ') or sep(σ'->σ) then cnt(σ)∩cnt(σ')=∅ for EVERY circuit
# (g(x,N) monotone: g(p_u) <= g(z')=0 kills all but one u of any block).  A pairwise-separated family => disjoint counted sets => MatchG.
import itertools, sys
def systems(n, S, hf):
    """hf: dict/func bitmask->0/1. returns list of (zmask, (p_u...), hz, (h(p_u)...)) with atoms restricted to minimal light/heavy."""
    S=list(S); rest=[v for v in range(n) if v not in S]; out=[]
    for r in range(len(rest)+1):
        for ones in itertools.combinations(rest,r):
            z=sum(1<<v for v in ones); hz=hf(z); opts=[]
            for u in S:
                o=[]; eu=1<<u
                if hf(eu)==0: o.append((eu,0))
                heavy=[]
                for k in range(len(ones)+1):
                    for T in itertools.combinations(ones,k):
                        p=eu|sum(1<<v for v in T)
                        if hf(p)==1 and not any(q&p==q for q in heavy): heavy.append(p)
                o+= [(p,1) for p in heavy]; opts.append(o)
            for combo in itertools.product(*opts):
                if hz==0 or sum(1 for p,hp in combo if hp==0)<=1:
                    out.append((z,tuple(p for p,_ in combo),hz,tuple(hp for _,hp in combo)))
    return out
def sep(a,b):
    z2,hz2=b[0],b[2]; bad=0
    for p,hp in zip(a[1],a[3]):
        if (p & ~z2) or hp<hz2: bad+=1
    return bad<=1
def compat(a,b): return sep(a,b) or sep(b,a)
def famsearch(n, sets, hf, limit=None):
    SY=[systems(n,S,hf) for S in sets]; m=len(sets)
    order=sorted(range(m),key=lambda w:len(SY[w])); ch=[None]*m; cache={}
    def rec(k, cand):
        if k==m: return True
        w=order[k]
        for a in cand[w]:
            ch[w]=a; nc=dict(cand); ok=True
            for j in range(k+1,m):
                v=order[j]; nc[v]=[b for b in cand[v] if compat(a,b)]
                if not nc[v]: ok=False; break
            if ok and rec(k+1,nc): return True
        return False
    r=rec(0,{w:SY[w] for w in range(m)})
    return ([ch[w] for w in range(m)] if r else None), [len(s) for s in SY]
def hf_of_circuit(c):
    from lib import ev
    n,G=c['n'],c['gates']; hw=[g for g in G if g[0]=='not'][0][1]; memo={}
    def hf(mask):
        if mask not in memo: memo[mask]=ev(n,G,[(mask>>v)&1 for v in range(n)])[hw]
        return memo[mask]
    return hf
def show(n,fam):
    return [('z1=%s'%[v for v in range(n) if a[0]>>v&1],'h(z)=%d'%a[2],[[v for v in range(n) if p>>v&1] for p in a[1]],a[3]) for a in fam]
if __name__=='__main__':
    import json
    for f in sys.argv[1:]:
        c=json.load(open(f)); tr=[s for s in c['sets'] if len(s)>=3]
        fam,sz=famsearch(c['n'],c['sets'],hf_of_circuit(c)); print(f,'systems',sz,'ALL sets: separated family', 'NONE' if fam is None else show(c['n'],fam))
