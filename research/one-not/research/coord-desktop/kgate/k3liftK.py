import itertools,json
C=json.load(open('research/one-not/data/witnesses/c4mono_k3.json')); n=C["n"]; sets=[tuple(s) for s in C["sets"]]; gl=C["gates"]; P=range(1<<n)
def ev(x):
    w=list(x)
    for g in gl: w.append(w[g[1]]&w[g[2]] if g[0]=='and' else w[g[1]]|w[g[2]])
    return w
V={A:ev([A>>u&1 for u in range(n)]) for A in P}; W=len(V[0])
ORs=[i for i in range(n,W) if gl[i-n][0]=='or']
def classes(Z,atoms):
    par={u:u for u in atoms}
    def f(x):
        while par[x]!=x: x=par[x]
        return x
    res=[]
    for k in range(W):
        if V[Z][k]: continue
        roots={f(u) for u in atoms if V[atoms[u]][k]}
        if len(roots)>=2:
            res.append(k); r=roots.pop()
            for q in roots: par[q]=r
    return res
menus=[]
for s in sets:
    comp=[i for i in range(n) if i not in s]; cl=set()
    for r in range(len(comp)+1):
        for Zs in itertools.combinations(comp,r):
            Z=sum(1<<i for i in Zs)
            subs=[sum(1<<i for i in c) for k in range(len(Zs)+1) for c in itertools.combinations(Zs,k)]
            for As in itertools.product(subs,repeat=len(s)):
                m=classes(Z,{u:A|1<<u for u,A in zip(s,As)})
                if len(m)==len(s)-1: cl.add(frozenset(m))
    menus.append(cl)
best=None
for k in (1,2,3,4):
    for K in itertools.combinations(ORs,k):
        K=set(K); tot=sum(min(len(c&K) for c in M) for M in menus)
        if best is None or tot-k>best[0]: best=(tot-k,k,sorted(K))
print("menu sizes",[len(M) for M in menus],"| max over |K|<=4 of (Σ_w min_lifted |class∩K|) - |K| =",best[0],"at k =",best[1],"K =",best[2])
