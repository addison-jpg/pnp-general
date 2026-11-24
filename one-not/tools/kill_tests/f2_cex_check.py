# Independent brute-force check of the F2 STEP at one Q, straight from the definition (no bit tables, no shared code).
# python3 -I one-not/tools/kill_tests/f2_cex_check.py FILE.json [Q as comma list]
import sys, json, itertools
d=json.load(open(sys.argv[1])); n=d['n']; S=d['sets']; G=d['gates']; outs=d['outs']
Q=[int(x) for x in sys.argv[2].split(',')] if len(sys.argv)>2 and sys.argv[2] else []
assert sum(g[0]=='not' for g in G)==1 and all(len(R)>=2 for R in S) and all(len(set(a)&set(b))<=1 for a,b in itertools.combinations(S,2))
def ev(x, notval=None):
    w=[(x>>i)&1 for i in range(n)]
    for g in G:
        if g[0]=='not': w.append(1-w[g[1]] if notval is None else notval)
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
V=[ev(x) for x in range(1<<n)]
assert all(V[x][o]==int(any((x>>u)&1 for u in R)) for x in range(1<<n) for o,R in zip(outs,S)), 'circuit incorrect'
ors=[n+k for k,g in enumerate(G) if g[0]=='or']
def F2(Qm):
    F=set()
    for R in S:
        m=sum(1<<u for u in R)
        if m&Qm: continue
        for Z in range(1<<n):
            if Z&Qm!=Qm or Z&m: continue
            z=V[Z]; at=[V[Z|1<<u] for u in R]
            for g in ors:
                if g in F or z[g]: continue
                if sum(a[g] for a in at)>=2: F.add(g)
    return F
Qm=sum(1<<v for v in Q); F=F2(Qm)
alive=[R for R in S if not (sum(1<<u for u in R)&Qm)]
base=sum(len(R)-1 for R in alive); pts=sorted({u for R in alive for u in R})
print(d.get('name'),'n',n,'gates',len(G),'Q',Q,'|F2(Q)|',len(F),'base(Q)',base)
ok=False
for v in pts:
    gain=len(F-F2(Qm|1<<v)); cost=sum(len(R)-1 for R in alive if v in R); ok|=gain>=cost
    print('  v',v,'gain',gain,'cost',cost,'GOOD' if gain>=cost else 'bad')
print('F2 STEP at Q:', 'holds' if ok else 'FAILS (no v with gain >= cost)')
# structural facts at the fixed circuit
C0=[ev(x,0) for x in range(1<<n)]; C1=[ev(x,1) for x in range(1<<n)]
col=lambda T,i: tuple(t[i] for t in T)
cols=[col(V,i) for i in range(n+len(G))]
print('R2 (no two gates with the same real function):', len(set(cols[n:]))==len(G))
print('R3 (no gate equal to an input):', not (set(cols[n:])&set(cols[:n])))
read={x for g in G for x in g[1:]}
print('R4 (every gate read or an output):', all((n+k in read) or (n+k in outs) for k in range(len(G))))
print("R5' (C_0 and C_1 each wrong on some output):", any(col(C0,o)!=cols[o] for o in outs) and any(col(C1,o)!=cols[o] for o in outs))
