import json, sys, itertools, random, collections
sys.path.insert(0,'../../w8')
from rl import *
from t2 import witness, cone
import importlib.util
spec=importlib.util.spec_from_file_location('verify','../../w8/verify.py'); 
src=open('../../w8/verify.py').read().split("if __name__")[0]; ns={}; exec(src,ns); verify=ns['verify']
D=dict(files())
def show(name,a,b,cfg):
    c=D[name]; Lc=L(c); n,N=Lc.n,Lc.N
    print('==',name,'n',n,'sets',c['sets'],'outs',c['outs']); print('gates',[(n+k,g) for k,g in enumerate(c['gates'])])
    print('independent verify.py:',verify(c),'essential',Lc.ess,'h0',Lc.h0,'h=',[x for x in range(N) if (Lc.hx>>x)&1][:12])
    out=[]
    for k,(c_,atoms) in zip((a,b),cfg):
        d=Lc.down(c_); Z=d|(d<<N); V,M,B=merges(Lc,Z,atoms,Lc.outs[k]); out.append((Z,atoms,V,set(M),B))
        print(' set',k,c['sets'][k],'ceiling c=',bin(c_),'atoms',{u:(bin(p%N),p//N) for u,p in atoms.items()},'merge gates',sorted(M))
    (Za,ata,Va,Ma,Ba),(Zb,atb,Vb,Mb,Bb)=out
    for g in sorted(Ma&Mb):
        cn=cone(Lc,g); ands=[w for w in cn if Lc.op(w)=='and']
        hy=[witness(Lc,g,Za|Zb,al) for al in [ata[u] for u in Ba(g)]+[atb[u] for u in Bb(g)]]
        print('  COLLISION gate',g,c['gates'][g-n],'B_a',set(Ba(g)),'B_b',set(Bb(g)),'cone',sorted(cn),'ANDs in cone',ands,'(hyp,witness) per atom',hy)
# (A) standard type-1 configurations (atoms (e_u,1)) on a data circuit with essential NOT
name='w7/bad.jsonl:63'; c=D[name]; Lc=L(c); n,N=Lc.n,Lc.N
found=False
for a,b in itertools.permutations(range(len(c['sets'])),2):
    if found: break
    for ca in range(N):
        if found: break
        if (Lc.hx>>ca)&1 or any((ca>>u)&1 for u in c['sets'][a]): continue
        for cb in range(N):
            if (Lc.hx>>cb)&1 or any((cb>>u)&1 for u in c['sets'][b]): continue
            ata={u:(1<<u)+N for u in c['sets'][a]}; atb={u:(1<<u)+N for u in c['sets'][b]}
            da=Lc.down(ca); db=Lc.down(cb)
            _,Ma,_=merges(Lc,da|da<<N,ata,Lc.outs[a]); _,Mb,_=merges(Lc,db|db<<N,atb,Lc.outs[b])
            for g in set(Ma)&set(Mb):
                if not [w for w in cone(Lc,g) if Lc.op(w)=='and'] and not set(c['sets'][a])&set(c['sets'][b]):
                    show(name,a,b,[(ca,ata),(cb,atb)]); found=True; break
            if found: break
print('found A:',found)
# (B) the note's own section-5 configuration: collision g = h OR x_p
for name in ['w7/bad.jsonl:51','w7/badT.jsonl:1']:
    c=D[name]; Lc=L(c); n,N=Lc.n,Lc.N; a,b=Lc.hform()
    cfg=[];ks=[]
    from t5 import check5
    print(name,'check5',check5(Lc,a,b),'h = x%d or x%d'%(a,b))
    best=None
    for k1,k2 in itertools.combinations(range(len(c['sets'])),2):
        cf=[]
        for k in (k1,k2):
            cc=N-1
            for u in set(c['sets'][k])|{a,b}: cc&=~(1<<u)
            cf.append((cc,{u:((1<<u) if u in (a,b) else (1<<u)+N) for u in c['sets'][k]}))
        d1=Lc.down(cf[0][0]); d2=Lc.down(cf[1][0])
        M1=merges(Lc,d1|d1<<N,cf[0][1],Lc.outs[k1],True)[1]; M2=merges(Lc,d2|d2<<N,cf[1][1],Lc.outs[k2],True)[1]
        if set(M1)&set(M2): show(name,k1,k2,cf)
