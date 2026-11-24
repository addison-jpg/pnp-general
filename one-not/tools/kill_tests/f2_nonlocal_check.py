# Independent check (numpy, no code shared with f2lib/canon) of count and STEP at EVERY cube Q, for the families
#   F2 (real witnesses), F5 (F2, gate in the cone of the output of the witness set), F1 (UC faces), F4 (F1 in the cone),
# with the locality class of each cube: const (h constant on the cube), var (h = x_a on the cube), nvar (h = NOT-free... = 1-x_a
# cannot happen for a wire read by the only NOT), nonlocal (h depends on >= 2 free inputs).
# STEP in the Lean form (GainF2): some v not in Q with |F(Q) \ F(Q+v)| >= sum of (|S_w|-1) over alive w through v
# (a v on no alive set has cost 0 and is good; reported separately as 'free').
# python3 -I one-not/tools/kill_tests/f2_nonlocal_check.py FILE.json
import sys, json, itertools
import numpy as np
def analyse(d, verbose=True):
    n=d['n']; S=d['sets']; G=d['gates']; outs=d['outs']; P=1<<n; idx=np.arange(P,dtype=np.int64)
    assert sum(g[0]=='not' for g in G)==1
    assert all(len(R)>=2 for R in S) and all(len(set(a)&set(b))<=1 for a,b in itertools.combinations(S,2))
    def ev(nv=None):
        W=[((idx>>i)&1).astype(bool) for i in range(n)]
        for g in G:
            if g[0]=='not': W.append(~W[g[1]] if nv is None else np.full(P,bool(nv)))
            elif g[0]=='and': W.append(W[g[1]]&W[g[2]])
            else: W.append(W[g[1]]|W[g[2]])
        return W
    W=ev(); W0=ev(0); W1=ev(1)
    for o,R in zip(outs,S):
        t=np.zeros(P,bool)
        for u in R: t|=W[u]
        assert (W[o]==t).all(), 'circuit incorrect'
    h=W[[g for g in G if g[0]=='not'][0][1]]
    cone=[]
    for o in outs:
        seen=set(); st=[o]
        while st:
            x=st.pop()
            if x in seen or x<n: continue
            seen.add(x); st+=G[x-n][1:]
        cone.append(seen)
    up=lambda T,a: T[idx|(1<<a)]
    ors=[n+k for k,g in enumerate(G) if g[0]=='or']
    fam={f:[] for f in ('F2','F5','F1','F4')}
    for g in ors:
        m={f:np.zeros(P,bool) for f in fam}
        for wi,R in enumerate(S):
            av=np.ones(P,bool)
            for u in R: av&=~W[u]
            cr=[up(W[g],u) for u in R]; c1=[up(W1[g],u) for u in R]; c0=[up(W0[g],u)&up(h,u) for u in R]
            two=lambda L: sum(x.astype(np.int8) for x in L)>=2
            r=~W[g]&av&two(cr); u1=(~h&~W1[g]&av&two(c1))|(~W0[g]&av&two(c0))
            m['F2']|=r; m['F1']|=u1
            if g in cone[wi]: m['F5']|=r; m['F4']|=u1
        for f in fam:
            a=m[f]
            for v in range(n): a=a|up(a,v)          # a[Q] = some witness zero point Z >= Q
            fam[f].append(a)
    alive=[np.ones(P,bool) for _ in S]; base=np.zeros(P,np.int32)
    for wi,R in enumerate(S):
        for u in R: alive[wi]&=~W[u]
        base+=alive[wi]*(len(R)-1)
    # locality of h on each cube: dep[v][Q] = h depends on x_v somewhere on the cube x_Q = 1 (v not in Q)
    ndep=np.zeros(P,np.int32)
    for v in range(n):
        a=(h!=up(h,v))&~W[v]
        for u in range(n): a=a|up(a,u)
        ndep+=(a&~W[v])
    res={}
    for f in fam:
        A=np.array(fam[f]); cnt=A.sum(0); good=np.zeros(P,bool); goodreal=np.zeros(P,bool)
        for v in range(n):
            gain=(A&~A[:,idx|(1<<v)]).sum(0); cost=np.zeros(P,np.int32)
            for wi,R in enumerate(S):
                if v in R: cost+=alive[wi]*(len(R)-1)
            free=~W[v]
            good|=free&(gain>=cost); goodreal|=free&(cost>0)&(gain>=cost)
        pos=base>0
        res[f]=dict(cubes=int(pos.sum()),count_fail=int((pos&(cnt<base)).sum()),step_fail=int((pos&~good).sum()),
            step_fail_nonlocal=int((pos&~good&(ndep>=2)).sum()),step_fail_onlyfree=int((pos&good&~goodreal).sum()),
            nonlocal_cubes=int((pos&(ndep>=2)).sum()),min_slack=int((cnt-base)[pos].min()),
            fail_Q=[int(q) for q in np.nonzero(pos&~good)[0][:20]],F_empty=int(cnt[0]),base_empty=int(base[0]),
            step_empty=bool(good[0]),count_fail_Q=[int(q) for q in np.nonzero(pos&(cnt<base))[0][:5]])
        if verbose: print(d.get('name'),f,res[f])
    return res
if __name__=='__main__': analyse(json.load(open(sys.argv[1])))
