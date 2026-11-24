# Check Gap-G on hard-case circuits: is there a per-set choice of test systems (type M/A(Q)/B)
# whose cone-masked counted wire sets are pairwise disjoint?
# Counted wires for (z, p) in the cone of o_S: wire(z)=0 and >= 2 u in S with wire(p_u)=1.
import json, itertools, sys, chargeok_check as K, conedbl, nsets
def systems(c, wi):
    n,S,G,outs=c['n'],[set(x) for x in c['sets']],c['gates'],c['outs']
    R=S[wi]; p=[k for k,g in enumerate(G) if g[0]=='not'][0]; nw=n+p; hw=G[p][1]
    ev=lambda x: K.evaluate(n,G,list(x))
    cone=K.cone(n,G,outs[wi]); Nin = nw in cone
    unit=lambda u: tuple(int(v==u) for v in range(n))
    zof=lambda Q: tuple(0 if v in Q else 1 for v in range(n))
    out=[]
    rest=[v for v in range(n) if v not in R]
    # type A(Q) for every Q ⊇ S that is Good (N not in cone, or h(z_Q)=0, or NOT false at all units)
    allunitsfalse = all(ev(unit(u))[nw]==0 for u in range(n))
    for r in range(len(rest)+1):
        for ex in itertools.combinations(rest,r):
            Q=R|set(ex); z=zof(Q)
            if Nin and not (ev(z)[nw]==1 or allunitsfalse): continue
            out.append(('A',tuple(sorted(Q)), z, {u:unit(u) for u in R}))
    # type B: z = z_S, p_u = e_u if h(e_u)=1 else z_{S minus u}
    if Nin:
        z=zof(R); pu={}
        for u in R:
            pu[u]= unit(u) if ev(unit(u))[hw]==1 else zof(R-{u})
        # validity T3: h(z)=0, or at most one u with h(p_u)=0 (with T2 automatically)
        if ev(z)[hw]==0 or sum(1 for u in R if ev(pu[u])[hw]==0)<=1:
            out.append(('B',None,z,pu))
    res=[]
    for typ,Q,z,pu in out:
        Wz=ev(z); Wp={u:ev(pu[u]) for u in R}
        # GoodT check on the cone-masked circuit for the NOT: true at z, or true at <=1 test point
        if Nin and not (Wz[nw]==1 or sum(1 for u in R if Wp[u][nw]==1)<=1): continue
        cnt=frozenset(i for i in cone if Wz[i]==0 and sum(1 for u in R if Wp[u][i]==1)>=2)
        res.append((typ,Q,cnt))
    return res
def gapg(c):
    m=len(c['sets']); opts=[systems(c,wi) for wi in range(m)]
    if any(not o for o in opts): return None
    # prune: keep distinct cnt sets per set, smallest first
    opts=[sorted({o[2]:o for o in os}.values(), key=lambda o:len(o[2])) for os in opts]
    def rec(i, used):
        if i==m: return []
        for o in opts[i]:
            if not (o[2] & used):
                r=rec(i+1, used|o[2])
                if r is not None: return [o]+r
        return None
    return rec(0, frozenset())
if __name__=='__main__':
    tot=0; ok=0; bad=[]
    for f in sys.argv[1:]:
        for l in open(f):
            c=conedbl.norm(json.loads(l)); r,_=nsets.analyse(c)
            if r!='BAD': continue
            tot+=1; sol=gapg(c)
            if sol: ok+=1
            elif len(bad)<3: bad.append(c)
    print('hard-case (BAD) circuits:',tot,'GapG choice found:',ok,'NO disjoint choice:',tot-ok)
    for c in bad: print('NO-CHOICE', json.dumps(c))
