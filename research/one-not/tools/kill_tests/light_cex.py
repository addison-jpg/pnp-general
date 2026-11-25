# Independent brute-force check (straight from the definition, no bit tricks) of UC(D,Q) and of both gains at the root.
# Run: python3 -I research/one-not/tools/kill_tests/light_cex.py research/one-not/data/witnesses/pappus_junk_gain.json
import json, itertools, sys
d=json.load(open(sys.argv[1])); n=d['n']; S=d['sets']; G=d['gates']; outs=d['outs']
assert sum(g[0]=='not' for g in G)==1
def ev(x, mode):  # x: frozenset of ones; mode 'real', 0, 1
    v=[1 if i in x else 0 for i in range(n)]
    for g in G:
        if g[0]=='not': v.append((1-v[g[1]]) if mode=='real' else mode)
        elif g[0]=='and': v.append(v[g[1]]&v[g[2]])
        else: v.append(v[g[1]]|v[g[2]])
    return v
pts=[frozenset(c) for k in range(n+1) for c in itertools.combinations(range(n),k)]
R={x:ev(x,'real') for x in pts}; C0={x:ev(x,0) for x in pts}; C1={x:ev(x,1) for x in pts}
ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; hi=G[ni-n][1]; h=lambda x:R[x][hi]
for o,Sw in zip(outs,S):
    assert all(R[x][o]==int(bool(x&set(Sw))) for x in pts)
for a,b in itertools.combinations(S,2): assert len(set(a)&set(b))<=1
ORS=[n+k for k,g in enumerate(G) if g[0]=='or']
def UC(D,Q):
    out=set()
    for Sw in S:
        if set(Sw)&Q or len(set(Sw)-D)<2: continue
        T=[u for u in Sw if u not in D]
        for Z in pts:
            if not Q<=Z or Z&(D|set(Sw)): continue
            for a,b in itertools.combinations(T,2):
                Za,Zb=Z|{a},Z|{b}
                for g in ORS:
                    if g in out: continue
                    if h(Z)==0 and C1[Z][g]==0 and C1[Za][g]==1 and C1[Zb][g]==1: out.add(g)
                    elif h(Za)==1 and h(Zb)==1 and C0[Z][g]==0 and C0[Za][g]==1 and C0[Zb][g]==1: out.add(g)
    return out
def base(D,Q): return sum(len(set(Sw)-D)-1 for Sw in S if not set(Sw)&Q and len(set(Sw)-D)>=2)
E=frozenset(); U=UC(E,E); b=base(E,E)
print('n',n,'gates',len(G),'|UC|',len(U),'base',b,'h(0)',h(E),'h(e_x)',[h(frozenset([x])) for x in range(n)],'h const?',len({h(x) for x in pts})==1)
for v in range(n):
    V=frozenset([v]); print('v',v,'x:=1 gain',len(U-UC(E,V)),'cost',b-base(E,V),'| x:=0 gain',len(U-UC(V,E)),'deg',b-base(V,E))
