src=open('tools/l951_charging/ov951.py').read().split('random.seed')[0]
exec(src)
import time, collections, itertools
from pysat.solvers import Glucose4
def analyse2(n,sets,gates,p):
    hw=gates[p][1]; full=(1<<n)-1
    W=lambda x: wires(n,gates,x); h=lambda x: W(x)[hw]
    mins=[x for x in range(1<<n) if h(x) and all(not h(x&~(1<<i)) for i in range(n) if x>>i&1)]
    T=None
    for k in range(n+1):
        for c in itertools.combinations(range(n),k):
            cm=sum(1<<i for i in c)
            if all(m&cm for m in mins): T=cm; break
        if T is not None: break
    per=[]; kinds=[]; cross=0
    for S in sets:
        sm=sum(1<<v for v in S)
        hard=any(not(m&sm) for m in mins); kinds.append('H' if hard else 'E')
        Z=full&~(sm|((T&~sm) if hard else 0))
        assert not h(Z)
        wZ=W(Z); wp={u:W(1<<u) for u in S}
        par={u:u for u in S}
        def f(x):
            while par[x]!=x: x=par[x]
            return x
        A=lambda w:[u for u in S if wp[u][w]] if wZ[w]==0 else None
        mg=[]
        for k,(op,a,b) in enumerate(gates):
            if op!='or' or wZ[n+k]!=0: continue
            Aa,Ab=A(a),A(b)
            if Aa and Ab and f(Aa[0])!=f(Ab[0]): par[f(Aa[0])]=f(Ab[0]); mg.append(k)
        assert len(mg)>=len(S)-1, (S,mg)
        per.append(mg)
    cnt=collections.Counter(k for mg in per for k in mg)
    dbl=sum(c-1 for k,c in cnt.items() if c>=2)
    return kinds,dbl
t0=time.time()
systems=[(5,[(0,1,2),(0,3,4)]),(5,[(0,1,2),(2,3),(3,4,0)]),(6,[(0,1),(2,3),(4,5),(0,2,4)]),(6,[(0,1,2),(3,4,5),(0,3)]),(6,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)])]
for n,sets in systems:
    base=sum(len(S)-1 for S in sets); stats=collections.Counter(); hh=0; nc=0
    for s in (base+2,base+3,base+4):
        for p in range(s-1):
            blocks=[]
            for it in range(5):
                if time.time()-t0>270: break
                cl,SEL,O=build(n,sets,s,p,blocks); S_=Glucose4(bootstrap_with=cl)
                if not S_.solve(): break
                gates,outs=decode(S_.get_model(),n,s,p,SEL,O); nc+=1
                kinds,dbl=analyse2(n,sets,gates,p); stats[dbl]+=1; hh+=kinds.count('H')>=2
                blocks.append([-SEL[k][0][gates[k][1]] for k in range(s)]+[-SEL[k][1][gates[k][2]] for k in range(s) if k!=p])
    print(sets,'circuits',nc,'with >=2 hard sets',hh,'double-merge histogram',dict(stats),flush=True)
