# SAT for the post-NOT block of a one-NOT circuit with a FIXED pre-NOT block (prefix gates over inputs; h = wire hw).
# Variables only for the k post-NOT gates (values at y=0 and y=1).  Options: essential, live (post gates and NOT read or output),
# clean (every post gate differs in REAL mode from every earlier wire, non-constant), symmetry (colex on post block).
import sys, itertools, json, time, threading
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def evalpre(n,pre):
    X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
    vals=[]
    for x in X:
        w=list(x)
        for g in pre:
            w.append(w[g[1]]&w[g[2]] if g[0]=='and' else w[g[1]]|w[g[2]])
        vals.append(w)
    return X,vals

def build(n,sets,pre,hw,k,ess=True,live=True,clean=True,sym=True,outs_pre=False,forbid_reads=None):
    P=IDPool(); cl=[]
    X,vals=evalpre(n,pre); NX=len(X)
    W0=n+len(pre)          # wires before NOT
    Nw=W0                  # NOT wire index
    hx=[vals[j][hw] for j in range(NX)]
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    def lit(i,j,m,pos=True):
        if i<W0: return bool(vals[j][i])==pos
        if i==Nw: return bool(m)==pos
        v=P.id(('v',i,j,m)); return v if pos else -v
    def real(i,j,pos=True):
        if i<W0: return bool(vals[j][i])==pos
        if i==Nw: return bool(1-hx[j])==pos
        return lit(i,j,1-hx[j],pos)
    post=[Nw+1+q for q in range(k)]
    for g in post:
        cand=list(range(g))
        if forbid_reads: cand=[i for i in cand if i not in forbid_reads]
        A={i:P.id(('a',g,i)) for i in cand}; B={i:P.id(('b',g,i)) for i in cand}
        cl.extend(CardEnc.equals(list(A.values()),1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(list(B.values()),1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in cand:
            for j2 in cand:
                if j2<=i: cl.append([-A[i],-B[j2]])
        t=P.id(('t',g))
        for m in (0,1):
            for j in range(NX):
                av=P.id(('A',g,j,m)); bv=P.id(('B',g,j,m)); v=P.id(('v',g,j,m))
                for i in cand:
                    addc([-A[i],lit(i,j,m,False),av]); addc([-A[i],lit(i,j,m,True),-av])
                    addc([-B[i],lit(i,j,m,False),bv]); addc([-B[i],lit(i,j,m,True),-bv])
                cl.append([-t,-v,av]); cl.append([-t,-v,bv]); cl.append([-t,v,-av,-bv])
                cl.append([t,v,-av]); cl.append([t,v,-bv]); cl.append([t,-v,av,bv])
    allw=list(range(W0))+[Nw]+post
    outc=[g for g in post]+([i for i in range(n,W0)] if outs_pre else [])
    O={}
    for w,S in enumerate(sets):
        Ow={g:P.id(('o',w,g)) for g in outc}; O[w]=Ow
        cl.extend(CardEnc.equals(list(Ow.values()),1,vpool=P,encoding=EncType.seqcounter).clauses)
        for g in outc:
            for j,x in enumerate(X):
                f=any(x[u] for u in S); addc([-Ow[g], real(g,j,f)])
    if ess:
        E0=[];E1=[]
        for w,S in enumerate(sets):
            for j,x in enumerate(X):
                f=any(x[u] for u in S)
                if f and not hx[j]:
                    e=P.id(('E0',w,j)); E0.append(e)
                    for g in outc: addc([-e,-O[w][g],lit(g,j,0,False)])
                if (not f) and hx[j]:
                    e=P.id(('E1',w,j)); E1.append(e)
                    for g in outc: addc([-e,-O[w][g],lit(g,j,1,True)])
        cl.append(E0); cl.append(E1)
    if live:
        for g in [Nw]+post:
            rd=[P.id(('a',g2,g)) for g2 in post if g2>g]+[P.id(('b',g2,g)) for g2 in post if g2>g]
            if g in post: rd+= [O[w][g] for w in O]
            cl.append(rd)
    if clean:
        for g in post:
            cl.append([real(g,j,True) for j in range(NX)]); cl.append([real(g,j,False) for j in range(NX)])
            for i in list(range(W0))+[Nw]:
                c=[real(g,j,not bool(vals[j][i]) if i<W0 else not bool(1-hx[j])) for j in range(NX)]
                addc(c)
            for g2 in post:
                if g2>=g: continue
                ds=[]
                for j in range(NX):
                    d=P.id(('d',g,g2,j)); ds.append(d)
                    r1=real(g,j); r2=real(g2,j)
                    addc([-d,r1,r2]); addc([-d,-r1 if not isinstance(r1,bool) else (not r1),-r2 if not isinstance(r2,bool) else (not r2)])
                cl.append(ds)
    if sym:
        for q in range(k-1):
            g=post[q]; g2=post[q+1]
            for i in range(g):
                for j2 in range(i): cl.append([-P.id(('b',g,i)),-P.id(('b',g2,j2))])
                for a1 in range(i):
                    for a2 in range(a1): cl.append([-P.id(('b',g,i)),-P.id(('b',g2,i)),-P.id(('a',g,a1)),-P.id(('a',g2,a2))])
    return P,cl,post,outc

def extract(P,model,n,sets,pre,hw,post,outc):
    ms=set(l for l in model if l>0)
    G=[list(g) for g in pre]+[['not',hw]]
    for g in post:
        a=[i for i in range(g) if P.id(('a',g,i)) in ms][0]; b=[i for i in range(g) if P.id(('b',g,i)) in ms][0]
        G.append(['and' if P.id(('t',g)) in ms else 'or',a,b])
    outs=[[g for g in outc if P.id(('o',w,g)) in ms][0] for w in range(len(sets))]
    return dict(n=n,sets=[list(S) for S in sets],gates=G,outs=outs)

def solve(n,sets,pre,hw,k,tmax=280,nsol=1,fo=None,**kw):
    t0=time.time(); P,cl,post,outc=build(n,sets,pre,hw,k,**kw)
    sv=Cadical153(bootstrap_with=cl); sols=[]; status=None
    while len(sols)<nsol:
        left=tmax-(time.time()-t0)
        if left<=0: status='TIMEOUT'; break
        tm=threading.Timer(left,lambda: sv.interrupt()); tm.start()
        r=sv.solve_limited(expect_interrupt=True); tm.cancel()
        if r is None: status='TIMEOUT'; break
        if r is False: status='UNSAT' if not sols else 'EXHAUSTED'; break
        c=extract(P,sv.get_model(),n,sets,pre,hw,post,outc); sols.append(c); status='SAT'
        if fo is not None: fo.write(json.dumps(c)+'\n'); fo.flush()
        ms=set(l for l in sv.get_model() if l>0); bl=[]
        for g in post:
            for i in range(g):
                if P.id(('a',g,i)) in ms: bl.append(-P.id(('a',g,i)))
                if P.id(('b',g,i)) in ms: bl.append(-P.id(('b',g,i)))
            bl.append(-P.id(('t',g)) if P.id(('t',g)) in ms else P.id(('t',g)))
        for w in range(len(sets)):
            for g in outc:
                if P.id(('o',w,g)) in ms: bl.append(-P.id(('o',w,g)))
        sv.add_clause(bl)
    sv.delete()
    return status,sols,time.time()-t0

# ---- prefixes computing Th_2 ----
def th2_tree(pairs):
    """pairs: list of 4 pairs (2-element lists) of inputs; returns gates (wire ids from 8) and h wire. Binary tree:
       leaf O=u|v, T=u&v; node O=O1|O2, T=T1|T2|(O1&O2)."""
    G=[]; n=8
    def add(op,a,b): G.append([op,min(a,b),max(a,b)]); return n+len(G)-1
    leaves=[]
    for u,v in pairs: leaves.append((add('or',u,v),add('and',u,v)))
    def node(L,R,needO=True):
        O=add('or',L[0],R[0]) if needO else None
        T=add('or',add('or',L[1],R[1]),add('and',L[0],R[0]))
        return (O,T)
    l=node(leaves[0],leaves[1]); r=node(leaves[2],leaves[3])
    root=node(l,r,needO=False)
    return G,root[1]
