# Heredity test for pure menus: restrict x_v := 0 for v outside V = V(F), NOT gate kept.
# Restricted I1 options are original I1 options (zero points vanish outside V): included trivially.
# Restricted I0: zero point (V \ S_w, 0) instead of (top_w, 0); atoms m_u | e_u, m_u a minterm of h inside V.
import sys, json, itertools, collections, functools
sys.argv=['x','.','10']
src=open('tools/kill_tests/canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
CAP=3000
st=collections.Counter(); wit=[]
for name,n,S,G,outs in circuits():
    if n>10 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); FULLPT=(1<<n)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    p=[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[p][1]]; hb=lambda x:(h>>x)&1
    mint=[x for x in range(1<<n) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
    graph=all(len(R)==2 for R in S)
    menu=[]
    for R in S:
        Rm=sum(1<<u for u in R); top=FULLPT&~Rm; rest=[v for v in range(n) if v not in R]; M=set()
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                if not hb(z): M|=merges(W1,n,G,R,z,{u:1<<u for u in R})
        per=[[m for m in mint if (m&Rm)&~(1<<u)==0] for u in R]
        for ms in itertools.islice(itertools.product(*per),CAP):
            M|=merges(W0,n,G,R,top,{u:ms[i]|1<<u for i,u in enumerate(R)})
        menu.append(M)
    st['circuits']+=1; st['graph']+=graph
    m=len(S)
    fams=[F for k in range(1,m) for F in itertools.combinations(range(m),k)] if m<=8 else [F for k in (1,2,3) for F in itertools.combinations(range(m),k)]
    for F in fams:
        Vm=0
        for w in F:
            for u in S[w]: Vm|=1<<u
        if Vm==FULLPT: continue
        st['families']+=1
        for w in F:
            R=S[w]; Rm=sum(1<<u for u in R); z=Vm&~Rm
            per=[[mm for mm in mint if (mm&~Vm)==0 and (mm&Rm)&~(1<<u)==0] for u in R]
            if any(not x for x in per): continue
            for ms in itertools.islice(itertools.product(*per),CAP):
                Mr=merges(W0,n,G,R,z,{u:ms[i]|1<<u for i,u in enumerate(R)})
                st['restricted I0 classes']+=1
                bad=Mr-menu[w]
                if bad:
                    st['FAIL']+=1; st['FAIL graph']+=graph
                    if len(wit)<8: wit.append(dict(name=name,n=n,graph=graph,F=F,w=w,S=S[w],V=[v for v in range(n) if Vm>>v&1],m=[[v for v in range(n) if mm>>v&1] for mm in ms],cls=sorted(Mr),notin=sorted(bad),menu=sorted(menu[w])))
print(dict(st))
for x in wit: print(x)
