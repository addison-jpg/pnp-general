# SAT generator for correct one-NOT circuits (lifted two-mode encoding).
# Canonical form: gates 0..pnot-1 = exactly the cone of h (every pre-NOT gate read inside the pre-NOT block or by the NOT),
# gate pnot = NOT, gates after: anything.  Values: pre-NOT gates one table, post-NOT gates tables for y=0 and y=1.
# Correctness:  F_w(x,0)=o_w(x) if h(x)=1,  F_w(x,1)=o_w(x) if h(x)=0.  Essential: C0 wrong and C1 wrong.
import sys, itertools, json, time, threading
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def build(n, sets, s, pnot, hfun=None, hcons=None, ess=True, live=True, sym=True, fixed=None, extra_outs_pre=True,
          forbid=None):
    """hfun: dict/func x(tuple)->0/1 fixes h. hcons: list of (x,val) constraints on free h. fixed: {k: ['and',a,b]} fixed gates.
       forbid: list of models' gate lists to block (exact structure)."""
    P=IDPool(); cl=[]
    X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    pre=lambda k: k<pnot
    def V(k,x,m):
        return P.id(('v',k,x)) if pre(k) else P.id(('v',k,x,m))
    def lit(i,x,m,pos=True):
        if i<n: return bool(x[i])==pos
        k=i-n
        if k==pnot: return bool(m)==pos
        v=V(k,x,m); return v if pos else -v
    modes=lambda k: (0,) if pre(k) else (0,1)
    sel={}
    for k in range(s):
        if k==pnot: continue
        g=n+k; cand=list(range(g))
        A=[P.id(('a',k,i)) for i in cand]; B=[P.id(('b',k,i)) for i in cand]
        sel[k]=(A,B)
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in cand:
            for j in range(i+1): cl.append([-A[i],-B[j]])     # a<b
        t=P.id(('t',k))
        for m in modes(k):
            for x in X:
                av=P.id(('A',k,x,m)); bv=P.id(('B',k,x,m)); v=V(k,x,m)
                for i in cand:
                    addc([-A[i], lit(i,x,m,False), av]); addc([-A[i], lit(i,x,m,True), -av])
                    addc([-B[i], lit(i,x,m,False), bv]); addc([-B[i], lit(i,x,m,True), -bv])
                cl.append([-t,-v,av]); cl.append([-t,-v,bv]); cl.append([-t,v,-av,-bv])
                cl.append([t,v,-av]); cl.append([t,v,-bv]); cl.append([t,-v,av,bv])
    # NOT input
    H=[P.id(('h',i)) for i in range(n+pnot)]
    cl.extend(CardEnc.equals(H,1,vpool=P,encoding=EncType.seqcounter).clauses)
    for i in range(n): cl.append([-H[i]])  # NOT reads a gate (else h is a variable: allowed? keep simple: forbid)
    if hfun is not None:
        for x in X:
            hv=hfun(x)
            for i in range(n,n+pnot): addc([-H[i], lit(i,x,0,bool(hv))])
        hval=lambda x: bool(hfun(x))
    else:
        for x in X:
            hx=P.id(('H',x))
            for i in range(n,n+pnot):
                addc([-H[i], lit(i,x,0,False), hx]); addc([-H[i], lit(i,x,0,True), -hx])
        for x,val in (hcons or []):
            cl.append([P.id(('H',tuple(x)))] if val else [-P.id(('H',tuple(x)))])
        hval=None
    # outputs
    m_=len(sets)
    O={}
    for w,S in enumerate(sets):
        Ow=[P.id(('o',w,k)) for k in range(s)]; O[w]=Ow
        cl.extend(CardEnc.equals(Ow,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.append([-Ow[pnot]])
        for k in range(s):
            if k==pnot: continue
            if pre(k) and not extra_outs_pre: cl.append([-Ow[k]]); continue
            for x in X:
                f=any(x[u] for u in S)
                if hval is not None:
                    mm=0 if hval(x) else 1
                    addc([-Ow[k], lit(n+k,x,mm,f)])
                else:
                    hx=P.id(('H',x))
                    addc([-Ow[k], -hx, lit(n+k,x,0,f)]); addc([-Ow[k], hx, lit(n+k,x,1,f)])
    if ess:
        E0=[];E1=[]
        for w,S in enumerate(sets):
            for x in X:
                f=any(x[u] for u in S)
                if f:
                    if hval is not None and hval(x): continue
                    e=P.id(('E0',w,x)); E0.append(e)
                    for k in range(pnot+1): cl.append([-e,-O[w][k]])
                    for k in range(pnot+1,s): addc([-e,-O[w][k],lit(n+k,x,0,False)])
                    if hval is None: cl.append([-e,-P.id(('H',x))])
                else:
                    if hval is not None and not hval(x): continue
                    e=P.id(('E1',w,x)); E1.append(e)
                    for k in range(pnot+1): cl.append([-e,-O[w][k]])
                    for k in range(pnot+1,s): addc([-e,-O[w][k],lit(n+k,x,1,True)])
                    if hval is None: cl.append([-e,P.id(('H',x))])
        cl.append(E0); cl.append(E1)
    if live:
        for k in range(s):
            g=n+k
            rd=[P.id(('a',k2,g)) for k2 in range(k+1,s) if k2!=pnot]+[P.id(('b',k2,g)) for k2 in range(k+1,s) if k2!=pnot]
            if k==pnot: cl.append(rd); continue
            if pre(k):
                rdp=[P.id(('a',k2,g)) for k2 in range(k+1,pnot)]+[P.id(('b',k2,g)) for k2 in range(k+1,pnot)]+[P.id(('h',g))]
                cl.append(rdp)
            else:
                cl.append(rd+[O[w][k] for w in range(m_)])
    if sym:
        for k in range(s-1):
            if k==pnot or k+1==pnot: continue
            g=n+k
            for i in range(g):
                for j in range(i): cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,j))])
                for a1 in range(i):
                    for a2 in range(a1): cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,i)),-P.id(('a',k,a1)),-P.id(('a',k+1,a2))])
    if fixed:
        for k,g in fixed.items():
            if g[0]=='not': continue
            cl.append([P.id(('t',k))] if g[0]=='and' else [-P.id(('t',k))])
            cl.append([P.id(('a',k,g[1]))]); cl.append([P.id(('b',k,g[2]))])
    for gl in (forbid or []):
        c=[]
        for k,g in enumerate(gl):
            if g[0]=='not': continue
            c+= [-P.id(('a',k,g[1])),-P.id(('b',k,g[2])), (-P.id(('t',k)) if g[0]=='and' else P.id(('t',k)))]
        cl.append(c)
    return P,cl

def extract(P,model,n,sets,s,pnot):
    ms=set(l for l in model if l>0); G=[]
    for k in range(s):
        if k==pnot:
            G.append(['not',[i for i in range(n+pnot) if P.id(('h',i)) in ms][0]]); continue
        a=[i for i in range(n+k) if P.id(('a',k,i)) in ms][0]; b=[i for i in range(n+k) if P.id(('b',k,i)) in ms][0]
        G.append(['and' if P.id(('t',k)) in ms else 'or',a,b])
    outs=[n+[k for k in range(s) if P.id(('o',w,k)) in ms][0] for w in range(len(sets))]
    return dict(n=n,sets=[list(S) for S in sets],gates=G,outs=outs)

def solve(n,sets,s,pnot,tmax=280,nsol=1,**kw):
    t0=time.time(); P,cl=build(n,sets,s,pnot,**kw); tb=time.time()-t0
    sv=Cadical153(bootstrap_with=cl); sols=[]; status=None
    while len(sols)<nsol:
        left=tmax-(time.time()-t0)
        if left<=0: status='TIMEOUT'; break
        tm=threading.Timer(left,lambda: sv.interrupt()); tm.start()
        r=sv.solve_limited(expect_interrupt=True); tm.cancel()
        if r is None: status='TIMEOUT'; break
        if r is False: status='UNSAT' if not sols else 'EXHAUSTED'; break
        c=extract(P,sv.get_model(),n,sets,s,pnot); sols.append(c); status='SAT'
        # block this exact gate structure
        bl=[]
        for k,g in enumerate(c['gates']):
            if g[0]=='not': continue
            bl+=[-P.id(('a',k,g[1])),-P.id(('b',k,g[2])),(-P.id(('t',k)) if g[0]=='and' else P.id(('t',k)))]
        sv.add_clause(bl)
    sv.delete()
    return status,sols,time.time()-t0,tb,len(cl)

def th2(vs):
    vs=list(vs); return lambda x: int(sum(x[v] for v in vs)>=2)
