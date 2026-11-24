#!/usr/bin/env python3
"""Check of Theorem H2 internals (NOTES.md section 5) for h = x_a OR x_b on constructed lifted circuits.
W1 classes: Z_w = down((c_w,1)), c_w = complement of S_w+{a,b}; atoms (e_a,0),(e_b,0),(e_u,1).
Verifies: |Mg_w| >= d_w; collisions only A-set/B-set through a common point p with B_w={a,p}, B_w'={b,p};
multiplicity <= 2; K <= pi; K <= 2*#outside; s-1 >= base - K//2 ... on every generated circuit (all verified correct)."""
import random, itertools, sys
def build(rng):
    # points: a=0,b=1, others 2..n-1. random A-sets / B-sets / N-sets, pairwise meeting in <=1 point
    n=rng.randint(6,10); pts=list(range(2,n)); sets=[]
    def okadd(S):
        return all(len(set(S)&set(T))<=1 for T in sets)
    for _ in range(30):
        k=rng.randint(1,3); typ=rng.choice('AABBN')
        S=sorted(rng.sample(pts,min(k+(typ=='N'),len(pts))))
        if typ=='A': S=[0]+S
        if typ=='B': S=[1]+S
        if len(S)>=2 and okadd(S): sets.append(S)
    if not sets: return None
    gates=[]  # lifted circuit M: inputs 0..n-1 = x, n = y ; gates ('or'/'and',i,j) wires n+1+idx
    def G(op,i,j): gates.append((op,i,j)); return n+len(gates)
    y=n; h=G('or',0,1)
    gp={}
    def getg(p):
        if p not in gp: gp[p]=G('or',h,p) if rng.random()<.8 else G('or',p,h)
        return gp[p]
    outs=[]
    yh=None
    for S in sets:
        rest=[u for u in S if u>1]; typ='A' if 0 in S else 'B' if 1 in S else 'N'
        mode=rng.choice(['honest','mux','mux','mux2']) if typ!='N' else rng.choice(['honest','honest','muxN'])
        if mode=='honest':
            w=S[0]
            order=S[1:]; rng.shuffle(order)
            for u in order: w=G('or',w,u)
            outs.append(w)
        else:
            # world-1 part: OR of g_p (shared, = h or x_p), world-0 corrector y or T_w
            ws=[getg(p) if rng.random()<.7 else p for p in rest]
            if all(x<n for x in ws): ws[0]=getg(rest[0])
            rng.shuffle(ws); w=ws[0]
            for x in ws[1:]: w=G('or',w,x)
            t=S[0]
            order=S[1:]; rng.shuffle(order)
            for u in order: t=G('or',t,u)
            c=G('or',y,t)
            outs.append(G('and',w,c))
    return n,sets,gates,outs
def tables(n,gates):
    N=1<<(n+1); full=(1<<N)-1
    W=[]
    for i in range(n+1):
        t=0
        for p in range(N):
            if (p>>i)&1: t|=1<<p
        W.append(t)
    for op,i,j in gates: W.append(W[i]|W[j] if op=='or' else W[i]&W[j])
    return W
def check(n,sets,gates,outs):
    W=tables(n,gates); N=1<<n
    pt=lambda x,l: x+N*l
    val=lambda t,x,l: (t>>pt(x,l))&1
    # correctness of the lifted spec at real points
    for S,o in zip(sets,outs):
        for x in range(N):
            hv=(x&1)|((x>>1)&1); ow=int(any((x>>u)&1 for u in S))
            if val(W[o],x,1-hv)!=ow: return None
    base=sum(len(S)-1 for S in sets)
    Mg=[]; 
    info=[]
    for S,o in zip(sets,outs):
        c=(N-1)
        for u in set(S)|{0,1}: c&=~(1<<u)
        inV=[val(t,c,1)==0 for t in W]
        atoms=[pt(1<<u,0 if u<2 else 1) for u in S]
        B=lambda w,S=S,atoms=atoms: frozenset(S[k] for k,a in enumerate(atoms) if (W[w]>>a)&1)
        # R_w: reachable down from output inside V
        R=set(); st=[o]
        assert inV[o]
        while st:
            w=st.pop()
            if w in R: continue
            R.add(w)
            if w>n:
                op,i,j=gates[w-n-1]
                for ch in (i,j):
                    if inV[ch]: st.append(ch)
        par={u:u for u in S}
        def f(a):
            while par[a]!=a: a=par[a]
            return a
        m=set()
        for w in sorted(R):
            if w<=n: assert len(B(w))<=1; continue
            op,i,j=gates[w-n-1]
            if op=='or':
                r1={f(u) for u in B(i)}; r2={f(u) for u in B(j)}
                assert len(r1)<=1 and len(r2)<=1
                if r1 and r2 and r1!=r2: par[r1.pop()]=r2.pop(); m.add(w)
            else: assert len({f(u) for u in B(w)})<=1
        assert len(m)>=len(S)-1
        Mg.append(m); info.append((S,B))
    cnt={}
    for k,m in enumerate(Mg):
        for g in m: cnt.setdefault(g,[]).append(k)
    K=0
    for g,ks in cnt.items():
        assert len(ks)<=2
        if len(ks)==2:
            K+=1
            (S1,B1),(S2,B2)=info[ks[0]],info[ks[1]]
            if 1 in S1: (S1,B1),(S2,B2)=(S2,B2),(S1,B1)
            assert 0 in S1 and 1 not in S1 and 1 in S2 and 0 not in S2
            p=set(S1)&set(S2); assert len(p)==1; p=p.pop()
            assert B1(g)=={0,p} and B2(g)=={1,p}
            assert val(W[g],1,0)==1 and val(W[g],2,0)==1   # g >= h at level 0
    A=[S for S in sets if 0 in S and 1 not in S]; Bs=[S for S in sets if 1 in S and 0 not in S]
    pi=sum(1 for p in range(2,n) if any(p in S for S in A) and any(p in S for S in Bs))
    outside=len(gates)-len(cnt)
    assert K<=pi and K<=2*outside and len(gates)>=base-K//2
    return dict(base=base,gates=len(gates),K=K,pi=pi,outside=outside)
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    T=int(sys.argv[2]) if len(sys.argv)>2 else 3000
    done=0; withK=0; maxK=0; minm=10**9
    while done<T:
        c=build(rng)
        if not c: continue
        r=check(*c)
        assert r is not None, 'constructed circuit incorrect'
        done+=1; withK+=r['K']>0; maxK=max(maxK,r['K']); minm=min(minm,r['outside']-r['K'])
    print('circuits',done,'with collisions',withK,'max K',maxK,'min(outside-K)',minm,'all asserts passed')
