# For SAT-generated live correct circuits: compare Lean min-D and generalized test systems (z,p_u).
import sys, time, itertools, collections
sys.path.insert(0,__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'../../../../tools/l951_charging')); sys.path.insert(0,'.')
import os; os.chdir(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'../../../..'))
import live951
from pysat.solvers import Cadical153
sys.path.insert(0,__import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from feas import systems
SYS={'k4e':(4,[(0,1),(0,2),(0,3),(1,2),(1,3)]),'c5':(5,[(0,1),(1,2),(2,3),(3,4),(4,0)]),'gadget':(5,[(0,1),(0,2),(3,4)]),
     'k4':(4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),'p2':(6,[(0,1,2),(0,3,4),(1,3),(2,4),(5,0)]),'pasch':(6,[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]),
     'tri':(3,[(0,1),(0,2),(1,2)]),'star':(4,[(0,1),(0,2),(0,3)]),'path':(4,[(0,1),(1,2),(2,3)]),'k4e2':(5,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,4),(3,4)])}
def cone(n,gates,o):
    c=set();st=[o]
    while st:
        w=st.pop()
        if w<n or w in c: continue
        c.add(w); st+=[gates[w-n][1],gates[w-n][2]]
    return c
def essential(n,sets,gates,outs):
    def wrong(c):
        for x in range(1<<n):
            w=[(x>>i)&1 for i in range(n)]
            for op,a,b in gates: w.append(c if op=='not' else (w[a]&w[b] if op=='and' else w[a]|w[b]))
            if any(w[o]!=int(any(x>>v&1 for v in S)) for S,o in zip(sets,outs)): return True
        return False
    return wrong(0) and wrong(1)
def analyse(n,sets,gates,outs,stats,report):
    s=len(gates); full=(1<<n)-1
    vals=[live951.wires(n,gates,x) for x in range(1<<n)]
    p=[k for k,g in enumerate(gates) if g[0]=='not'][0]; Nw=n+p; hw=gates[p][1]
    hset=frozenset(x for x in range(1<<n) if vals[x][hw])
    if 0 in hset: return
    if ESS and not essential(n,sets,gates,outs): return
    stats['ess']+=1
    # Lean min
    lean=0; gopts=[]
    for S,o in zip(sets,outs):
        oc=cone(n,gates,o); Sm=sum(1<<v for v in S); rest=[v for v in range(n) if v not in S]; best=None
        for r in range(len(rest)+1):
            for R in itertools.combinations(rest,r):
                z=full&~(Sm|sum(1<<v for v in R))
                if Nw in oc and vals[z][Nw]==0: continue
                D=sum(1 for w in oc if vals[z][w]==0 and sum(vals[1<<u][w] for u in S)>=2)
                best=D if best is None else min(best,D)
        lean+=best
        opts=set()
        for z,hz,pp in systems(n,S,hset):
            if Nw not in oc and z!=full&~Sm: continue
            D=frozenset(w for w in oc if vals[z][w]==0 and sum(vals[pp[u][0]][w] for u in S)>=2)
            opts.add(D)
        # keep only inclusion-minimal options
        opts=[D for D in opts if not any(E<D for E in opts)]
        gopts.append(opts)
    stats['lean_slack',min(s-lean,4)]+=1
    # min excess over generalized choices (cap product)
    best=None; bestsum=None
    for ch in itertools.islice(itertools.product(*gopts),20000):
        mult=collections.Counter(w for D in ch for w in D)
        ex=sum(c-1 for c in mult.values() if c>1)
        if best is None or ex<best: best=ex
        sm=sum(len(D) for D in ch)
        if bestsum is None or sm<bestsum: bestsum=sm
        if best==0: break
    stats['gen_minexcess',best]+=1
    if best>0 and report[0]<5:
        report[0]+=1; print('  GEN-EXCESS',best,sets,'gates',gates,'outs',outs,'h minterms',sorted(m for m in hset if all((m&~(1<<i)) not in hset for i in range(n) if m>>i&1)),flush=True)
ESS=False
def run(name,sizes,CAP,SECS):
    n,sets=SYS[name]; base=sum(len(S)-1 for S in sets); t0=time.time()
    stats=collections.Counter(); report=[0]
    for d in sizes:
        s=base+d
        for p in range(s-1):
            cl,SEL,O=live951.build_live(n,sets,s,p,[])
            for k in range(s):
                if k!=p: cl+=[[-SEL[k][0][i],-SEL[k][1][i]] for i in range(n+k)]
            sol=Cadical153(bootstrap_with=cl); found=0
            while found<CAP and time.time()-t0<SECS:
                if not sol.solve(): break
                M=sol.get_model(); gates,outs=live951.decode(M,n,s,p,SEL,O); found+=1; stats['tot']+=1
                pos=set(l for l in M if l>0)
                sol.add_clause([-SEL[k][0][gates[k][1]] for k in range(s)]+[-SEL[k][1][gates[k][2]] for k in range(s) if k!=p]
                               +[(-SEL[k][2] if SEL[k][2] in pos else SEL[k][2]) for k in range(s) if k!=p])
                analyse(n,sets,gates,outs,stats,report)
            sol.delete()
    print(name,sizes,dict(stats),f'{time.time()-t0:.0f}s',flush=True)
if __name__=='__main__':
    ESS="--ess" in sys.argv; sys.argv=[a for a in sys.argv if a!="--ess"]
    name=sys.argv[1]; sizes=tuple(int(x) for x in sys.argv[2].split(',')); CAP=int(sys.argv[3]); SECS=float(sys.argv[4])
    run(name,sizes,CAP,SECS)
