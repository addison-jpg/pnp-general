# SAT: min size correct one-NOT circuit with ESSENTIAL NOT (C0 wrong and C1 wrong), live, h(0)=0 optional
import sys, itertools, json, time, threading
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
def build(n, sets, s, essential=True, h0=True, clean=False, maxand=None):
    P=IDPool(); cl=[]
    X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
    copies=['r','0','1'] if essential else ['r']
    def lit(c,i,x,pos=True):
        if i<n: return bool(x[i])==pos
        v=P.id(('v',c,i,x)); return v if pos else -v
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    NK=[P.id(('n',k)) for k in range(s)]
    cl.extend(CardEnc.equals(NK,1,vpool=P,encoding=EncType.seqcounter).clauses)
    for k in range(s):
        g=n+k
        A=[P.id(('a',k,i)) for i in range(g)]; B=[P.id(('b',k,i)) for i in range(g)]
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(g):
            for j in range(i+1): cl.append([-A[i],-B[j],NK[k]])
        for i in range(g): cl.append([-NK[k],-A[i],B[i]])
        t=P.id(('t',k)); cl.append([-NK[k],-t])
        for c in copies:
          for x in X:
            av=P.id(('A',c,k,x)); bv=P.id(('B',c,k,x))
            for i in range(g):
                addc([-A[i], lit(c,i,x,False), av]); addc([-A[i], lit(c,i,x,True), -av])
                addc([-B[i], lit(c,i,x,False), bv]); addc([-B[i], lit(c,i,x,True), -bv])
            v=P.id(('v',c,g,x))
            cl.append([-t,-v,av]); cl.append([-t,-v,bv]); cl.append([-t,v,-av,-bv])
            cl.append([t,NK[k],v,-av]); cl.append([t,NK[k],v,-bv]); cl.append([t,NK[k],-v,av,bv])
            if c=='r':
                cl.append([-NK[k],v,av]); cl.append([-NK[k],-v,-av])
                if h0 and x==X[0]: cl.append([-NK[k],v])
            elif c=='0': cl.append([-NK[k],-v])
            else: cl.append([-NK[k],v])
    if maxand is not None: cl.extend(CardEnc.atmost([P.id(('t',k)) for k in range(s)],maxand,vpool=P,encoding=EncType.seqcounter).clauses)
    W0=[];W1=[]
    for w,S in enumerate(sets):
        Ow=[P.id(('o',w,k)) for k in range(s)]
        cl.extend(CardEnc.equals(Ow,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for k in range(s):
            cl.append([-Ow[k],-NK[k]])
            for x in X: addc([-Ow[k], lit('r',n+k,x,any(x[u] for u in S))])
        if essential:
            for x in X:
                if any(x[u] for u in S):
                    e=P.id(('w0',w,x)); W0.append(e)
                    for k in range(s): cl.append([-e,-Ow[k],-P.id(('v','0',n+k,x))])
                else:
                    e=P.id(('w1',w,x)); W1.append(e)
                    for k in range(s): cl.append([-e,-Ow[k],P.id(('v','1',n+k,x))])
    if essential: cl.append(W0); cl.append(W1)
    if clean:
        for k in range(s):
            g=n+k
            cl.append([P.id(('v','r',g,x)) for x in X]); cl.append([-P.id(('v','r',g,x)) for x in X])
            for i in range(g):
                D=[]
                for x in X:
                    d=P.id(('d',g,i,x)); D.append(d)
                    addc([-d, lit('r',g,x,True), lit('r',i,x,True)]); addc([-d, lit('r',g,x,False), lit('r',i,x,False)])
                cl.append(D)
    for k in range(s-1):
        g=n+k
        for i in range(g):
            for j in range(i): cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,j))])
    for k in range(s):
        g=n+k
        cl.append([P.id(('a',k2,g)) for k2 in range(k+1,s)]+[P.id(('b',k2,g)) for k2 in range(k+1,s)]+[P.id(('o',w,k)) for w in range(len(sets))])
    return P,cl
def extract(P,model,n,sets,s):
    ms=set(l for l in model if l>0); gates=[]
    for k in range(s):
        g=n+k
        a=[i for i in range(g) if P.id(('a',k,i)) in ms][0]; b=[i for i in range(g) if P.id(('b',k,i)) in ms][0]
        if P.id(('n',k)) in ms: gates.append(['not',a])
        else: gates.append(['and' if P.id(('t',k)) in ms else 'or',a,b])
    outs=[[n+k for k in range(s) if P.id(('o',w,k)) in ms][0] for w in range(len(sets))]
    return dict(n=n,sets=[list(S) for S in sets],gates=gates,outs=outs)
def solve(n,sets,s,tmax=200,**kw):
    kw.setdefault('clean',CLEAN)
    t0=time.time(); P,cl=build(n,sets,s,**kw)
    sv=Cadical153(bootstrap_with=cl)
    tm=threading.Timer(tmax,lambda: sv.interrupt()); tm.start()
    res=sv.solve_limited(expect_interrupt=True); tm.cancel()
    out=extract(P,sv.get_model(),n,sets,s) if res else None
    return res,out,time.time()-t0
CLEAN=False
if __name__=='__main__':
    CLEAN=len(sys.argv)>5
    n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); tmax=int(sys.argv[4]) if len(sys.argv)>4 else 200
    base=sum(len(S)-1 for S in sets)
    for ex in [int(e) for e in sys.argv[3].split(',')]:
        res,out,t=solve(n,sets,base+ex,tmax=tmax)
        print('n',n,sets,'base',base,'s',base+ex,'res',res,'sec %.0f'%t,flush=True)
        if out: print(json.dumps(out)); break
