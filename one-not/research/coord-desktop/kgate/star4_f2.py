import sys,os,json,itertools; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from n1sat import solve
n=4; sets=[(0,1),(0,2),(0,3)]; hterms=[0b0110,0b1010,0b1100]
P=range(1<<n); FULL=(1<<(1<<n))-1
tt=[sum(1<<A for A in P if A>>u&1) for u in range(n)]; gl=[]
def add(k,f,a,b=None):
    tt.append(f&FULL); gl.append([k,a] if b is None else [k,a,b]); return len(tt)-1
def AND(ws):
    w=ws[0]
    for x in ws[1:]: w=add('and',tt[w]&tt[x],w,x)
    return w
def OR(ws):
    w=ws[0]
    for x in ws[1:]: w=add('or',tt[w]|tt[x],w,x)
    return w
hw=OR([AND([u for u in range(n) if m>>u&1]) for m in hterms])
N=add('not',~tt[hw],hw); hv=lambda A: tt[hw]>>A&1
fun,sel=solve(n,sets,hv,2)
def real(points):
    ps=set(points); terms=[]
    for A in ps:
        if any((A&~(1<<u)) in ps and hv(A&~(1<<u))==hv(A) for u in range(n) if A>>u&1): continue
        vs=[u for u in range(n) if A>>u&1]
        terms.append(AND(vs) if hv(A) else AND([N]+vs))
    return OR(terms)
for G in (1,0):
    s=real(fun[(G,'s')]); t=real(fun[(G,'t')]); add('or',tt[s]|tt[t],s,t)
outs=[OR(list(s)) for s in sets]
C={"n":n,"sets":[list(s) for s in sets],"gates":gl,"outs":outs}
json.dump(C,open('star4.json','w'))
def ev(x):
    w=list(x)
    for g in C["gates"]:
        if g[0]=='not': w.append(1-w[g[1]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
vals={A:ev([A>>u&1 for u in range(n)]) for A in P}
for A in P:
    for s,o in zip(sets,outs): assert vals[A][o]==int(any(A>>u&1 for u in s))
nots=sum(g[0]=='not' for g in gl); print("JSON ok: correct, gates",len(gl),"NOTs",nots,"base",sum(len(s)-1 for s in sets))
ORs=[n+i for i,g in enumerate(gl) if g[0]=='or']
def F2(Q):
    res=set()
    for wi,s in enumerate(sets):
        if any(Q>>u&1 for u in s): continue
        for Z in P:
            if Z&Q!=Q or any(Z>>u&1 for u in s): continue
            for g in ORs:
                if vals[Z][g]: continue
                if sum(vals[Z|1<<u][g] for u in s)>=2: res.add(g)
    return res
F=F2(0); base=sum(len(s)-1 for s in sets); print("|F2(∅)| =",len(F),"vs base",base)
for v in range(n):
    cost=sum(len(s)-1 for s in sets if v in s)
    gain=len(F-F2(1<<v)); print(" v=%d cost %d gain %d %s"%(v,cost,gain,"OK" if gain>=cost else "FAIL"))
