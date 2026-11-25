# monotone sandwich complexities sand0(h), sand1(h): min #AND/OR gates s.t. lo_w <= out_w <= hi_w (outputs may be inputs or constants: cost counted as 0)
import sys, itertools, json, time, random
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
def solve(n, bounds, s, X, ess=None):
    # bounds: list of (lo,hi) dict x->0/1 ; wires: const0, const1, inputs, gates
    P=IDPool(); cl=[]
    nw=n+2
    def lit(i,x,pos=True):
        if i==0: return (not pos)
        if i==1: return pos
        if i<nw: return bool(x[i-2])==pos
        v=P.id(('v',i,x)); return v if pos else -v
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    for k in range(s):
        g=nw+k
        A=[P.id(('a',k,i)) for i in range(g)]; B=[P.id(('b',k,i)) for i in range(g)]
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(g):
            for j in range(i+1): cl.append([-A[i],-B[j]])
        t=P.id(('t',k))
        for x in X:
            av=P.id(('A',k,x)); bv=P.id(('B',k,x))
            for i in range(g):
                addc([-A[i], lit(i,x,False), av]); addc([-A[i], lit(i,x,True), -av])
                addc([-B[i], lit(i,x,False), bv]); addc([-B[i], lit(i,x,True), -bv])
            v=P.id(('v',g,x))
            cl.append([-t,-v,av]); cl.append([-t,-v,bv]); cl.append([-t,v,-av,-bv])
            cl.append([t,v,-av]); cl.append([t,v,-bv]); cl.append([t,-v,av,bv])
    for w,(lo,hi) in enumerate(bounds):
        Ow=[P.id(('o',w,i)) for i in range(nw+s)]
        cl.extend(CardEnc.equals(Ow,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(nw+s):
            for x in X:
                if lo[x]: addc([-Ow[i], lit(i,x,True)])
                if not hi[x]: addc([-Ow[i], lit(i,x,False)])
    if ess is not None:
        # ess = list over w of target o_w on X (points incl. y as last coord); need some (w,x,y=0) with F<o and some (w,x,y=1) with F>o
        E0=[];E1=[]
        for w,o in enumerate(ess):
            for x in X:
                if x[-1]==0 and o[x]==1 and not bounds[w][0][x]:
                    e=P.id(('e0',w,x)); E0.append(e)
                    for i in range(nw+s): addc([-e,-P.id(('o',w,i)),lit(i,x,False)])
                if x[-1]==1 and o[x]==0 and bounds[w][1][x]:
                    e=P.id(('e1',w,x)); E1.append(e)
                    for i in range(nw+s): addc([-e,-P.id(('o',w,i)),lit(i,x,True)])
        cl.append(E0); cl.append(E1)
    sv=Cadical153(bootstrap_with=cl); r=sv.solve(); sv.delete(); return r
def sand(n,sets,h,X,smax):
    A=[{x:int(any(x[u] for u in S)) for x in X} for S in sets]
    b0=[({x:a[x]&h[x] for x in X},a) for a in A]
    b1=[(a,{x:a[x]|h[x] for x in X}) for a in A]
    res=[]
    for b in (b0,b1):
        for s in range(smax+1):
            if solve(n,b,s,X): res.append(s); break
        else: res.append(smax+1)
    return res
def monotone_fns(n):
    X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
    # enumerate via antichains recursively (Dedekind): f on n vars = (f0,f1) with f0<=f1
    def rec(k):
        if k==0: return [(0,),(1,)]
        prev=rec(k-1); out=[]
        for f0 in prev:
            for f1 in prev:
                if all(a<=b for a,b in zip(f0,f1)): out.append(f0+f1)
        return out
    return X,rec(n)
if __name__=='__main__':
    n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); N=int(sys.argv[3]); random.seed(1)
    X,F=monotone_fns(n); base=sum(len(S)-1 for S in sets)
    F=[f for f in F if f[0]==0 and any(f)]
    if N<len(F): F=random.sample(F,N)
    t0=time.time(); worst=None; hist={}
    for f in F:
        h=dict(zip(X,f)); s0,s1=sand(n,sets,h,X,base)
        hist[(s0,s1)]=hist.get((s0,s1),0)+1
        if max(s0,s1)<base: print("FN-RELEVANT max<base", s0,s1,f,flush=True)
        if worst is None or s0+s1<worst[0]: worst=(s0+s1,s0,s1,f); print('new min sum',s0+s1,'sand0',s0,'sand1',s1,'h minterm table',f,flush=True)
        if time.time()-t0>250: print('time cap'); break
    print(sets,'base',base,'tested',sum(hist.values()),'hist (sand0,sand1):count',sorted(hist.items()))
