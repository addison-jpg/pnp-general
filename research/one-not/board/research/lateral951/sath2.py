#!/usr/bin/env python3
"""SAT search for H2 violations: h = x_0 OR x_1 fixed (gate 0 of the lifted circuit M).
Asks: is there a monotone AND/OR circuit M over x_0..x_{n-1}, y with G gates, gate 0 = x_0|x_1, and outputs
F_w with F_w=1 on U_w, F_w=0 on V_w (lifted spec)?  Real circuit size s = G+1.
H2 (s >= base+1) is violated iff SAT at G = base-1;  951 is refuted iff SAT at G = base-2.
Usage: sath2.py '<sets as python list>' G [timeout_s]"""
import sys, itertools, time, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc
def search(n,sets,G,timeout=None,verbose=False,force_h=True):
    N=1<<n; hv=lambda q:(q&1)|((q>>1)&1)
    hit=lambda q,S: any((q>>u)&1 for u in S)
    ones=[];zeros=[];pts=set()
    for S in sets:
        U=[(q,1) for q in range(N) if hit(q,S)]+[(q,0) for q in range(N) if hit(q,S) and hv(q)]
        V=[(q,0) for q in range(N) if not hit(q,S)]+[(q,1) for q in range(N) if not hit(q,S) and not hv(q)]
        ones.append(U);zeros.append(V);pts|=set(U)|set(V)
    pts=sorted(pts); pid={p:i for i,p in enumerate(pts)}
    cnt=[0]
    def nv(): cnt[0]+=1; return cnt[0]
    cl=[]
    nin=n+1
    inval=lambda i,p: ((p[0]>>i)&1) if i<n else p[1]
    v=[[nv() for _ in pts] for _ in range(G)]
    T=[nv() for _ in range(G)]  # true = AND
    s1=[[nv() for _ in range(nin+k)] for k in range(G)]
    s2=[[nv() for _ in range(nin+k)] for k in range(G)]
    A=[[nv() for _ in pts] for _ in range(G)]
    B=[[nv() for _ in pts] for _ in range(G)]
    def onehot(xs):
        cl.append(list(xs))
        for a,b in itertools.combinations(xs,2): cl.append([-a,-b])
    for k in range(G):
        onehot(s1[k]); onehot(s2[k])
        # first input index < second
        for i in range(nin+k):
            for j in range(i+1):
                cl.append([-s1[k][i],-s2[k][j]])
        for sel,X in ((s1[k],A[k]),(s2[k],B[k])):
            for i in range(nin+k):
                for pi,p in enumerate(pts):
                    if i<nin:
                        cl.append([-sel[i], X[pi] if inval(i,p) else -X[pi]])
                    else:
                        w=v[i-nin][pi]
                        cl.append([-sel[i],-w,X[pi]]); cl.append([-sel[i],w,-X[pi]])
        for pi in range(len(pts)):
            a,b,o,t=A[k][pi],B[k][pi],v[k][pi],T[k]
            # AND
            cl+= [[-t,-o,a],[-t,-o,b],[-t,o,-a,-b]]
            # OR
            cl+= [[t,o,-a],[t,o,-b],[t,-o,a,b]]
    # gate 0 = x0 | x1
    if force_h: cl+= [[-T[0]],[s1[0][0]],[s2[0][1]]]
    # every gate except outputs is used: skip (not needed for existence)
    # symmetry: gates k>=1 ordered by (second input) nondecreasing lexicographic is unsafe with fixed gate 0; skip.
    out=[[nv() for _ in range(G)] for _ in sets]
    for w,S in enumerate(sets):
        onehot(out[w])
        for k in range(G):
            for p in ones[w]: cl.append([-out[w][k], v[k][pid[p]]])
            for p in zeros[w]: cl.append([-out[w][k],-v[k][pid[p]]])
    # usage: each gate k is read by a later gate or is an output (WLOG for minimal G; valid since removing unused gates only shrinks... keeps search space smaller; if SAT with fewer gates exists, pad is impossible, so we run increasing G)
    solver=Cadical153(bootstrap_with=cl)
    t0=time.time()
    r=solver.solve()
    if not r: return None, time.time()-t0
    m=set(x for x in solver.get_model() if x>0)
    gates=[]
    for k in range(G):
        i=[i for i in range(nin+k) if s1[k][i] in m][0]; j=[j for j in range(nin+k) if s2[k][j] in m][0]
        gates.append(('and' if T[k] in m else 'or',i,j))
    outs=[[k for k in range(G) if out[w][k] in m][0]+nin for w in range(len(sets))]
    return dict(n=n,sets=sets,lift_gates=gates,lift_outs=outs), time.time()-t0
def to_real(sol):
    """lifted (inputs x, y=wire n) -> one-NOT circuit JSON: gate0=h, then NOT, then the rest."""
    n=sol['n']; lg=sol['lift_gates']
    # lifted wire ids: 0..n-1 x, n = y, n+1+k gate k.  real: 0..n-1 x, n = h (gate0), n+1 = NOT, n+2+(k-1) gate k>=1
    def m(wi):
        if wi<n: return wi
        if wi==n: return n+1
        k=wi-n-1
        return n if k==0 else n+1+k
    gates=[['or',0,1],['not',n]]+[[op,m(i),m(j)] for op,i,j in lg[1:]]
    return dict(n=n,sets=[list(S) for S in sol['sets']],gates=gates,outs=[m(o) for o in sol['lift_outs']])
if __name__=='__main__':
    sets=eval(sys.argv[1]); G=int(sys.argv[2]); n=max(max(S) for S in sets)+1
    sol,t=search(n,sets,G)
    base=sum(len(S)-1 for S in sets)
    print('n',n,'base',base,'G',G,'(s=%d)'%(G+1),'SAT' if sol else 'UNSAT','%.1fs'%t)
    if sol: print(json.dumps(to_real(sol)))
