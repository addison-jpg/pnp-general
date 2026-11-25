# test of claim (iii): section 5 (h = x_a OR x_b), independent implementation of 5.2-5.4 with every proof step asserted
import sys, random, collections, json, itertools
from rl import *
def check5(Lc,a,b,rng=None,nmaps=3):
    rng=rng or random.Random(0)
    n,N,W=Lc.n,Lc.N,Lc.W; S=Lc.S; m=len(S)
    assert Lc.linear and Lc.correct and Lc.hx==(Lc.xv[a]|Lc.xv[b])
    typ=['AB' if (a in x and b in x) else 'A' if a in x else 'B' if b in x else 'N' for x in S]
    assert typ.count('AB')<=1
    Zs=[];At=[];Rs=[];Ms=[];Bs=[]
    for k,Sx in enumerate(S):
        c=(N-1)
        for u in set(Sx)|{a,b}: c&=~(1<<u)
        d=Lc.down(c); Z=d|(d<<N)
        atoms={u:((1<<u) if u in (a,b) else (1<<u)+N) for u in Sx}
        R,M,B=merges(Lc,Z,atoms,Lc.outs[k],restrictR=True)
        V2,M2,_=merges(Lc,Z,atoms,Lc.outs[k],restrictR=False)
        Zs.append(Z);At.append(atoms);Rs.append(R);Ms.append(set(M));Bs.append(B)
    van=lambda w,k:(W[w]&Zs[k])==0
    # 5.3 crossing table for ALL wires
    for k in range(m):
        for k2 in range(m):
            if k==k2: continue
            P=set(S[k])&(set(S[k2])|{a,b})
            for w in range(len(W)):
                if van(w,k2): assert Bs[k](w)<=P, 'crossing table'
    cnt=collections.defaultdict(list)
    for k in range(m):
        for g in Ms[k]: cnt[g].append(k)
    coll=collections.defaultdict(list)  # A-set -> [(g,p)]
    K=0
    for g,ks in cnt.items():
        assert len(ks)<=2, 'gate in 3 merge sets'
        if len(ks)==2:
            K+=1; k1,k2=ks
            if typ[k1]!='A': k1,k2=k2,k1
            assert typ[k1]=='A' and typ[k2]=='B', 'collision types'
            p=set(S[k1])&set(S[k2]); assert len(p)==1; p=p.pop(); assert p not in (a,b)
            assert Bs[k1](g)=={a,p} and Bs[k2](g)=={b,p}
            assert Lc.val(g,1<<a,0) and Lc.val(g,1<<b,0)
            coll[k1].append((g,p))
    pi=sum(1 for p in range(n) if p not in (a,b) and any(p in S[k] for k in range(m) if typ[k]=='A') and any(p in S[k] for k in range(m) if typ[k]=='B'))
    assert K<=pi, 'K<=pi'
    for k,l in coll.items(): assert len({p for g,p in l})==len(l), 'distinct points'
    allM=set(cnt); gates=Lc.gatew; outside=[w for w in gates if w not in allM]
    base=Lc.base
    assert len(allM)==base-K
    # 5.4 chain argument, for several parent maps
    for _ in range(nmaps):
        tops={}; junc=set(); ands=set()
        for k,l in coll.items():
            R=Rs[k]; out=Lc.outs[k]
            assert Lc.val(out,1<<b,0)==0
            par={}
            cands=collections.defaultdict(list)
            for w in R:
                if w>=n and w!=Lc.yw:
                    for c in Lc.ch(w):
                        if c in R: cands[c].append(w)
            for w in R:
                if w!=out:
                    assert cands[w], 'R_w wire without parent in R_w'
                    par[w]=rng.choice(cands[w])
            chains=[]; gset={g for g,p in l}
            chil=collections.defaultdict(set)
            mytops=set()
            for g,p in l:
                assert Lc.val(g,1<<b,0)==1
                ch=[g]; w=g
                while True:
                    assert w!=out, 'reached F_w without AND'
                    q=par[w]
                    if Lc.op(q)=='and': break
                    assert Lc.op(q)=='or'
                    chil[q].add(w); w=q; ch.append(w)
                    assert (W[g]&~W[w])==0
                for x in ch:
                    assert {a,p}<=Bs[k](x)
                    assert x==g or x not in gset, 'g_j on chain of g_i'
                    assert x in R
                T=par[ch[-1]]; mytops.add(ch[-1]); ands.add(T)
                assert ch[-1] not in tops or tops[ch[-1]]==(k,T), 'top shared between A-sets'
                tops[ch[-1]]=(k,T)
            J={q for q,cs in chil.items() if len(cs)>=2}
            assert len(mytops)+len(J)==len(l), ('forest count',len(mytops),len(J),len(l))
            for q in J:
                assert q not in allM, 'junction in a merge set'
                for k2 in range(m):
                    if k2!=k: assert not van(q,k2), 'junction vanishes on another Z'
                assert q not in junc
                junc.add(q)
        assert not (junc&ands)
        for T in ands: assert T not in allM
        percnt=collections.Counter(T for (k,T) in tops.values())
        assert all(v<=2 for v in percnt.values()), 'AND carries >2 tops'
        assert len(tops)+len(junc)==K
        assert K<=len(junc)+2*len(ands)<=2*len(outside)
    sM=len(gates)
    assert 2*len(outside)>=K
    assert sM>=base-K//2, 'BOUND'
    return dict(K=K,pi=pi,outside=len(outside),sM=sM,base=base,slack=sM-base,ess=Lc.ess,marg=len(outside)-K)
if __name__=='__main__':
    st=collections.Counter(); rng=random.Random(1)
    for name,c in files():
        if c['n']>16: continue
        Lc=L(c)
        if not Lc.ok or not Lc.correct: st['skip']+=1; continue
        st['circ']+=1
        if Lc.h0: st['h0=1']+=1; continue
        hf=Lc.hform()
        # also: h = single variable, h = AND of two, other
        if hf is None: st['h other']+=1; continue
        st['h=xa|xb']+=1
        r=check5(Lc,hf[0],hf[1],rng)
        st['K>0']+=r['K']>0; st['ess']+=r['ess']; st['pi>0']+=r['pi']>0
        st['minslack']=min(st.get('minslack',99),r['slack']); st['maxK']=max(st['maxK'],r['K']); st['maxpi']=max(st['maxpi'],r['pi'])
        if r['K']: print(name,r)
    print(dict(st))
