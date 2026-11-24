#!/usr/bin/env python3
"""Step-by-step check of the proof of THEOREM H2 (NOTES.md section 8) on lifted circuits with h = x_0 OR x_1.
Input: n, sets, lifted gates [(op,i,j)] over wires 0..n-1 = x, n = y, n+1+k = gate k, outs (wire ids).
Checks, as asserts: delivered union-find gives exactly d_w merges; collision table; for every A-set w with
collisions g_i: p_i-live path to F_w, b-kill AND T_i (private), label union-find junction ORs (outside every
merge set, private), #J_w + #T_w >= k_w; K <= #outside; hence gates >= base."""
import sys, json, random
def analyse(n,sets,gates,outs):
    NW=n+1+len(gates); N=1<<n
    W=[]
    for i in range(n+1):
        t=0
        for p in range(2*N):
            if (p>>i)&1: t|=1<<p
        W.append(t)
    for op,i,j in gates: W.append(W[i]|W[j] if op=='or' else W[i]&W[j])
    val=lambda w,x,l: (W[w]>>(x+N*l))&1
    hv=lambda x:(x&1)|((x>>1)&1)
    for S,o in zip(sets,outs):
        for x in range(N):
            if val(o,x,1-hv(x))!=int(any((x>>u)&1 for u in S)): return None
    parents=[[] for _ in range(NW)]
    for k,(op,i,j) in enumerate(gates):
        parents[i].append(n+1+k); parents[j].append(n+1+k)
    ch=lambda w: gates[w-n-1][1:]
    isor=lambda w: w>n and gates[w-n-1][0]=='or'
    atom=lambda u:(1<<u,0 if u<2 else 1)
    def per_set(S,o):
        c=N-1
        for u in set(S)|{0,1}: c&=~(1<<u)
        inV=[val(w,c,1)==0 for w in range(NW)]
        assert inV[o]
        live=lambda w,u: val(w,*atom(u))==1
        def down(root,u):
            """wires in V, u-live, with an upward path to root inside (V, u-live); returns parent pointers"""
            if not (inV[root] and live(root,u)): return {}
            par={root:None}; st=[root]
            while st:
                w=st.pop()
                if w>n:
                    for x in ch(w):
                        if x not in par and inV[x] and live(x,u): par[x]=w; st.append(x)
            return par
        D={u:down(o,u) for u in S}
        for u in S: assert o in D[u]
        Delta=lambda w: frozenset(u for u in S if w in D[u])
        blk={u:u for u in S}
        def f(a):
            while blk[a]!=a: a=blk[a]
            return a
        Mg=[]
        for w in range(NW):
            if not inV[w]: continue
            r={f(u) for u in Delta(w)}
            if w<=n: assert len(Delta(w))<=1 and w!=n
            assert len(r)<=2
            if len(r)==2:
                assert isor(w); a_,b_=r; blk[a_]=b_; Mg.append(w)
        assert len(Mg)==len(S)-1 and len({f(u) for u in S})==1
        return dict(S=S,o=o,inV=inV,D=D,Delta=Delta,Mg=Mg,live=live,down=down)
    info=[per_set(S,o) for S,o in zip(sets,outs)]
    owner={}
    for k,I in enumerate(info):
        for g in I['Mg']: owner.setdefault(g,[]).append(k)
    allMg=set(owner)
    K=0; coll={k:[] for k in range(len(sets))}
    for g,ks in owner.items():
        assert len(ks)<=2
        if len(ks)==2:
            K+=1
            ka,kb=ks if 0 in sets[ks[0]] else ks[::-1]
            Sa,Sb=sets[ka],sets[kb]
            assert 0 in Sa and 1 not in Sa and 1 in Sb and 0 not in Sb
            p=set(Sa)&set(Sb); assert len(p)==1; p=p.pop()
            assert info[ka]['Delta'](g)=={0,p} and info[kb]['Delta'](g)=={1,p}
            assert val(g,2,0)==1   # g(e_b,0)=1
            coll[ka].append((g,p))
    paid=set()
    for k,I in enumerate(info):
        cs=coll[k]
        if not cs: continue
        S=I['S']; assert len({p for g,p in cs})==len(cs)
        Ts=set(); xi=[]
        for g,p in cs:
            w=g
            while val(w,2,0)==1: prev=w; w=I['D'][p][w]; assert w is not None
            T=w; assert not isor(T) and T>n and I['inV'][T] and I['live'](T,p)
            assert T not in paid; Ts.add(T); xi.append(prev)
        paid|=Ts
        lam=[I['down'](x,p) for x,(g,p) in zip(xi,cs)]
        cls=list(range(len(cs)))
        def f2(a):
            while cls[a]!=a: a=cls[a]
            return a
        J=set()
        for w in range(NW):
            if not I['inV'][w]: continue
            r={f2(j) for j in range(len(cs)) if w in lam[j]}
            assert len(r)<=2
            if len(r)==2:
                assert isor(w) and w not in allMg and w not in paid
                a_,b_=r; cls[a_]=b_; J.add(w)
        paid|=J
        assert len(J)+len(Ts)>=len(cs)
    outside=len(gates)-len(allMg)
    base=sum(len(S)-1 for S in sets)
    assert len(paid)>=K and paid.isdisjoint(allMg) and outside>=K and len(gates)>=base
    return dict(base=base,G=len(gates),K=K,outside=outside,paid=len(paid))
if __name__=='__main__':
    import hor2, sath2
    mode=sys.argv[1]
    tot=0; withK=0; maxK=0; tight=0
    if mode=='constructed':
        rng=random.Random(int(sys.argv[2])); T=int(sys.argv[3])
        while tot<T:
            c=hor2.build(rng)
            if not c: continue
            r=analyse(*c); assert r is not None
            tot+=1; withK+=r['K']>0; maxK=max(maxK,r['K']); tight+=(r['outside']==r['K'])
    elif mode=='sat':   # SAT solutions with slack gates: sets from sath2_log.jsonl, G = base+extra
        extra=int(sys.argv[2]); lim=int(sys.argv[3]); seen=set()
        for line in open('sath2_log.jsonl'):
            r=json.loads(line); key=json.dumps(r['sets'])
            if key in seen: continue
            seen.add(key)
            if len(seen)>lim: break
            sol,t=sath2.search(r['n'],r['sets'],r['base']+extra)
            if not sol: continue
            a=analyse(sol['n'],sol['sets'],sol['lift_gates'],sol['lift_outs']); assert a is not None
            tot+=1; withK+=a['K']>0; maxK=max(maxK,a['K']); tight+=(a['outside']==a['K'])
    print(mode,sys.argv[2:],'circuits',tot,'with collisions',withK,'max K',maxK,'outside==K',tight,'all asserts passed')
