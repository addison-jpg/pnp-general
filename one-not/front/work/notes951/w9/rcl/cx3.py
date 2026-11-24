import json, sys, itertools, random, collections
from rl import *
from t2 import witness, cone
from t5 import check5
import adv5
src=open('../../w8/verify.py').read().split("if __name__")[0]; ns={}; exec(src,ns); verify=ns['verify']
def show(name,c,a,b,cfg):
    Lc=L(c); n,N=Lc.n,Lc.N
    print('==',name,'n',n,'sets',c['sets'],'outs',c['outs']); print('gates',[(n+k,g) for k,g in enumerate(c['gates'])])
    print('independent verify.py:',verify(c),'essential',Lc.ess,'h(0)=',Lc.h0,'hform',Lc.hform())
    out=[]
    for k,(c_,atoms) in zip((a,b),cfg):
        d=Lc.down(c_); Z=d|(d<<N); V,M,B=merges(Lc,Z,atoms,Lc.outs[k]); out.append((Z,atoms,V,set(M),B))
        print(' set',k,c['sets'][k],'ceiling c=',[v for v in range(n) if (c_>>v)&1],'atoms',{u:([v for v in range(n) if (p>>v)&1],p//N) for u,p in atoms.items()},'merge gates',sorted(M))
    (Za,ata,Va,Ma,Ba),(Zb,atb,Vb,Mb,Bb)=out
    for g in sorted(Ma&Mb):
        cn=cone(Lc,g); ands=[w for w in cn if Lc.op(w)=='and']
        hy=[witness(Lc,g,Za|Zb,al) for al in [ata[u] for u in Ba(g)]+[atb[u] for u in Bb(g)]]
        print('  COLLISION gate',g,c['gates'][g-n],'B_a',set(Ba(g)),'B_b',set(Bb(g)),'cone',sorted(cn),'ANDs in cone',ands,'(hyp,witness) per atom',hy)
rng=random.Random(5); foundA=False
for name,c in files():
    if foundA: break
    if c['n']>9: continue
    Lc=L(c)
    if not(Lc.ok and Lc.correct and Lc.ess and not Lc.h0): continue
    n,N=Lc.n,Lc.N; S=c['sets']
    for a,b in itertools.permutations(range(len(S)),2):
        if foundA: break
        if set(S[a])&set(S[b]): continue
        for _ in range(0):
            cs=[]
            for k in (a,b):
                cc=0; o=[v for v in range(n) if v not in S[k]]; rng.shuffle(o)
                for v in o:
                    if rng.random()<.6 and not (Lc.hx>>(cc|1<<v))&1: cc|=1<<v
                cs.append(cc)
            ata={u:(1<<u)+N for u in S[a]}; atb={u:(1<<u)+N for u in S[b]}
            da=Lc.down(cs[0]); db=Lc.down(cs[1])
            Ma=merges(Lc,da|da<<N,ata,Lc.outs[a])[1]; Mb=merges(Lc,db|db<<N,atb,Lc.outs[b])[1]
            if any(not [w for w in cone(Lc,g) if Lc.op(w)=='and'] for g in set(Ma)&set(Mb)):
                print('### (A) disjoint sets, standard type-1 configurations (ceiling c, atoms (e_u,1)), essential NOT')
                show(name,c,a,b,[(cs[0],ata),(cs[1],atb)]); foundA=True; break
for name,c in files():
    if foundA: break
    if c['n']>9: continue
    Lc=L(c)
    if not(Lc.ok and Lc.correct and Lc.ess and not Lc.h0): continue
    n,N=Lc.n,Lc.N; S=c['sets']
    for k,g in enumerate(c['gates']):
        if foundA: break
        if g[0]!='or' or g[1]>=n or g[2]>=n: continue
        u,u2=g[1],g[2]
        for a,b in itertools.permutations(range(len(S)),2):
            if u in S[a] and u2 in S[a] and not set(S[a])&set(S[b]):
                t,t2=S[b][0],S[b][1]
                ata={v:(1<<v)+N for v in S[a]}; atb={v:(1<<v)+N for v in S[b]}; atb[t]|=1<<u; atb[t2]|=1<<u2
                Ma=merges(Lc,3|3<<N if False else (1|1<<N),ata,Lc.outs[a])[1]; Mb=merges(Lc,1|1<<N,atb,Lc.outs[b])[1]
                if n+k in Ma and n+k in Mb:
                    print("### (A) disjoint sets, type-1 configurations with ceiling c=0 (Z={(0,0),(0,1)}), essential NOT")
                    show(name,c,a,b,[(0,ata),(0,atb)]); foundA=True; json.dump(c,open('cx_use_A.json','w')); break
print('foundA',foundA)
rng=random.Random(7); foundB=False
while not foundB:
    c=adv5.build(rng)
    if not c: continue
    v=adv5.valid(c)
    if not v: continue
    c,Lc=v
    if not Lc.ess or len(c['gates'])>16 or not verify(c)['clean']: continue
    r=check5(Lc,0,1)
    if r['K']<1: continue
    n,N=Lc.n,Lc.N; S=c['sets']
    for k1,k2 in itertools.combinations(range(len(S)),2):
        cf=[]
        for k in (k1,k2):
            cc=N-1
            for u in set(S[k])|{0,1}: cc&=~(1<<u)
            cf.append((cc,{u:((1<<u) if u<2 else (1<<u)+N) for u in S[k]}))
        d1=Lc.down(cf[0][0]); d2=Lc.down(cf[1][0])
        M1=merges(Lc,d1|d1<<N,cf[0][1],Lc.outs[k1],True)[1]; M2=merges(Lc,d2|d2<<N,cf[1][1],Lc.outs[k2],True)[1]
        if any(not [w for w in cone(Lc,g) if Lc.op(w)=='and'] for g in set(M1)&set(M2)):
            print('### (B) the note\'s own section-5.2 configuration, h = x0 or x1, essential NOT'); print('check5',r)
            show('constructed',c,k1,k2,cf); foundB=True; json.dump(c,open('cx_use_B.json','w')); break
