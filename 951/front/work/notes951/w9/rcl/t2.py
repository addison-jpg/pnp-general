# test of claim (ii): AND-witness lemma 2.3 and its "Use" on S2.2 collisions
import sys, random, collections, json
from rl import *
def configs(Lc,k,rng,num):
    n,N=Lc.n,Lc.N; Sx=Lc.S[k]; hx=Lc.hx; out=[]
    allm=N-1; Sm=sum(1<<u for u in Sx)
    for _ in range(num):
        if rng.random()<.5:
            Z=Lc.lo
            for u in Sx: Z&=~Lc.xv[u]
            atoms={}; ok=True; lvl1=rng.choice(Sx) if rng.random()<.3 else None
            for u in Sx:
                p=1<<u
                if u==lvl1:
                    p|=rng.getrandbits(n)&~Sm&allm if rng.random()<.5 else 0
                    atoms[u]=p+N; continue
                others=[v for v in range(n) if v not in Sx]; rng.shuffle(others)
                if rng.random()<.5: p|=rng.getrandbits(n)&~Sm&allm
                for v in others:
                    if (hx>>p)&1: break
                    p|=1<<v
                if not (hx>>p)&1: ok=False; break
                atoms[u]=p
            if ok: out.append(('t0',Z,atoms))
        else:
            c=0; others=[v for v in range(n) if v not in Sx]; rng.shuffle(others)
            mode=rng.random()
            for v in others:
                if mode<.15: break
                if mode>.6 and rng.random()<.3: continue
                if not (hx>>(c|1<<v))&1: c|=1<<v
            if (hx>>c)&1: continue
            d=Lc.down(c); Z=d|(d<<N)
            Qfree=[v for v in range(n) if not (c>>v)&1 and v not in Sx]; rng.shuffle(Qfree)
            atoms={}
            for u in Sx:
                p=1<<u
                if rng.random()<.4: p|=rng.getrandbits(n)&c
                if Qfree and rng.random()<.35: p|=1<<Qfree.pop()
                l=1
                if (hx>>p)&1 and rng.random()<.5: l=0
                atoms[u]=p+N*l
            out.append(('t1',Z,atoms))
    return out
def witness(Lc,g,Z,alpha):
    """returns (hyp, concl_first, concl_any): concl_first = AND G reachable from g via wires vanishing on Z and 1 at alpha,
       G vanishing, G(alpha)=1, with a child not vanishing."""
    W=Lc.W; van=lambda w:(W[w]&Z)==0; one=lambda w:(W[w]>>alpha)&1
    hyp=not any(van(i) and one(i) for i in Lc.inputs)
    seen=set(); st=[g]; found=False
    while st:
        w=st.pop()
        if w in seen: continue
        seen.add(w)
        if w<Lc.n or w==Lc.yw: continue
        cs=Lc.ch(w)
        if Lc.op(w)=='and' and any(not van(c) for c in cs): found=True
        for c in cs:
            if van(c) and one(c): st.append(c)
    return hyp,found
def cone(Lc,g):
    seen=set(); st=[g]
    while st:
        w=st.pop()
        if w in seen: continue
        seen.add(w)
        if w>=Lc.n and w!=Lc.yw: st+=Lc.ch(w)
    return seen
def run(seed=1,ncfg=3,npairs=12,maxn=12):
    rng=random.Random(seed); st=collections.Counter(); ex={}
    for name,c in files():
        if c['n']>maxn: st['skip_n']+=1; continue
        Lc=L(c)
        if not Lc.ok: st['skip_not']+=1; continue
        if not Lc.correct: st['incorrect']+=1; continue
        if Lc.h0: st['h0=1']+=1; continue
        st['circ']+=1; st['ess']+=Lc.ess; st['linear']+=Lc.linear
        cf=[]
        for k in range(len(Lc.S)):
            r=[]
            for (t,Z,atoms) in configs(Lc,k,rng,ncfg):
                try: V,M,B=merges(Lc,Z,atoms,Lc.outs[k])
                except AssertionError as e: st['S2.1 assert:'+str(e)[:30]]+=1; ex.setdefault('s21',(name,k,t,str(e))); continue
                st['cfg']+=1; r.append((t,Z,atoms,V,set(M),B))
            cf.append(r)
        prs=[(a,b) for a in range(len(Lc.S)) for b in range(a+1,len(Lc.S))]; rng.shuffle(prs)
        for a,b in prs[:npairs]:
            for ca in cf[a]:
                for cb in cf[b]:
                    ta,Za,ata,Va,Ma,Ba=ca; tb,Zb,atb,Vb,Mb,Bb=cb; Z=Za|Zb
                    # S2.2 check
                    Pab={u for u,p in ata.items() if not ((Zb>>p)&1 or any(False for _ in ()))}
                    # "atom below a point of Z_b": Z_b is a down-set here, so below iff member
                    for g in Va&Vb:
                        assert Ba(g)<=Pab
                    both=Va&Vb
                    for g in both:
                        if g<Lc.n or g==Lc.yw: continue
                        ba,bb=Ba(g),Bb(g)
                        iscoll=len(ba)>=2 and len(bb)>=2; ism=g in Ma and g in Mb
                        als=[ata[u] for u in ba]+[atb[u] for u in bb]
                        if not als: continue
                        res=[witness(Lc,g,Z,al) for al in als]
                        for hyp,found in res:
                            st['lemma_inst']+=1
                            if hyp:
                                st['lemma_hyp']+=1
                                if not found: st['LEMMA_VIOL']+=1; ex.setdefault('lemmaviol',(name,a,b,g))
                        if iscoll:
                            st['coll_whole']+=1; st['coll_merge']+=ism
                            cn=cone(Lc,g)
                            ands=[w for w in cn if Lc.op(w)=='and']
                            anyhyp=any(h for h,f in res)
                            if not anyhyp:
                                st['coll_nohyp']+=1; st['coll_nohyp_merge']+=ism
                            if not ands:
                                st['coll_noAND_in_cone']+=1; st['coll_noAND_merge']+=ism
                                if ism and (('cx' not in ex) or (Lc.ess and not ex['cx'][-1])):
                                    ex['cx']=(name,a,b,g,ta,tb,{u:(p%Lc.N,p//Lc.N) for u,p in ata.items()},{u:(p%Lc.N,p//Lc.N) for u,p in atb.items()},Lc.ess)
                            elif not any(w in both for w in ands):
                                st['coll_noAND_in_VaVb']+=1
                            st['coll_%s%s'%(ta,tb)]+=1
                            pure0=ta=='t0' and tb=='t0' and all(p<Lc.N for p in ata.values()) and all(p<Lc.N for p in atb.values())
                            if pure0:
                                st['pure00_coll']+=1; st['pure00_nohyp']+=not anyhyp; st['pure00_noAND']+=not ands
                                assert anyhyp and ands
                            std11=ta=='t1' and tb=='t1' and all(p==(1<<u)+Lc.N for u,p in ata.items()) and all(p==(1<<u)+Lc.N for u,p in atb.items())
                            if std11:
                                st['std11_coll']+=1; st['std11_nohyp']+=not anyhyp; st['std11_noAND']+=not ands
                                if not ands and ism and Lc.ess: ex.setdefault('cx11',(name,a,b,g,bin(Za&Lc.lo).count('1'),bin(Zb&Lc.lo).count('1')))
                            if not ands: st['noAND_%s%s'%(ta,tb)]+=1
    return st,ex
if __name__=='__main__':
    st,ex=run(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    for k in sorted(st): print(k,st[k])
    print(json.dumps(ex,default=str))
