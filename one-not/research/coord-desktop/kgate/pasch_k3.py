import sys,os,itertools,json; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from n1sat import solve
n=6; sets=[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]; P=range(1<<n); FULL=(1<<(1<<n))-1
fun,_=solve(n,sets,lambda A:0,3)
def build(order):
    tt=[sum(1<<A for A in P if A>>u&1) for u in range(n)]; gl=[]
    def add(k,f,a,b): tt.append(f&FULL); gl.append([k,a,b]); return len(tt)-1
    def AND(ws):
        w=ws[0]
        for x in ws[1:]: w=add('and',tt[w]&tt[x],w,x)
        return w
    def OR(ws):
        w=ws[0]
        for x in ws[1:]: w=add('or',tt[w]|tt[x],w,x)
        return w
    def real(ps):
        ps=set(ps); return OR([AND([u for u in range(n) if A>>u&1]) for A in ps if not any((A&~(1<<u)) in ps for u in range(n) if A>>u&1)])
    K=[]
    for G in order:
        s=real(fun[(G,'s')]); t=real(fun[(G,'t')]); K.append(add('or',tt[s]|tt[t],s,t))
    outs=[OR(list(s)) for s in sets]
    return {"n":n,"sets":[list(s) for s in sets],"gates":gl,"outs":outs},K
def analyse(C,K):
    gl=C["gates"]
    def ev(x):
        w=list(x)
        for g in gl: w.append(w[g[1]]&w[g[2]] if g[0]=='and' else w[g[1]]|w[g[2]])
        return w
    V={A:ev([A>>u&1 for u in range(n)]) for A in P}; W=len(V[0])
    for A in P:
        for s,o in zip(sets,C["outs"]): assert V[A][o]==int(any(A>>u&1 for u in s))
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
    realM=[];liftM=[]
    for s in sets:
        comp=[i for i in range(n) if i not in s]; rl=[];lf=set()
        for r in range(len(comp)+1):
            for Zs in itertools.combinations(comp,r):
                Z=sum(1<<i for i in Zs)
                rl.append(frozenset(classes(Z,{u:Z|1<<u for u in s})))
                subs=[sum(1<<i for i in c) for k in range(len(Zs)+1) for c in itertools.combinations(Zs,k)]
                for As in itertools.product(subs,repeat=len(s)):
                    m=classes(Z,{u:A|1<<u for u,A in zip(s,As)})
                    if len(m)==len(s)-1: lf.add(frozenset(m))
        realM.append(rl); liftM.append(lf)
    Ks=set(K); mreal=[min(len(c&Ks) for c in M) for M in realM]
    best=None
    for k in (1,2,3):
        for KK in itertools.combinations(ORs,k):
            KK=set(KK); tot=sum(min(len(c&KK) for c in M) for M in liftM)
            if best is None or tot-k>best[0]: best=(tot-k,k)
    return len(gl),mreal,len(set().union(*[c for M in realM for c in M])),len(set().union(*liftM)),best
base=sum(len(s)-1 for s in sets)
for order in itertools.permutations(range(3)):
    C,K=build(order); g,mr,ur,ul,b=analyse(C,K)
    print(order,"gates",g,"base",base,"real m",mr,"Σ",sum(mr),"| union real",ur,"| union lifted",ul,"| lifted max(Σ-|K|), |K|<=3:",b[0])
    if sum(mr)>3: json.dump(C,open('pasch_mono_k3_%s.json'%''.join(map(str,order)),'w'))
