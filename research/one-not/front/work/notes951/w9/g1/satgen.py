# SAT: correct one-NOT circuit of size s for sets; options: readcap (readers(x_v) <= deg(v)-cap), h0, live
import sys, itertools, json, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
def build(n, sets, s, readcap=None, nnot=1, h0=True, extra=None, capvars=None):
    P=IDPool(); cl=[]
    X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
    def lit(i,x,pos=True):
        if i<n: return bool(x[i])==pos
        v=P.id(('v',i,x)); return v if pos else -v
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    NK=[P.id(('n',k)) for k in range(s)]
    if nnot==1: cl.extend(CardEnc.equals(NK,1,vpool=P,encoding=EncType.seqcounter).clauses)
    else:
        for k in range(s): cl.append([-NK[k]])
    for k in range(s):
        g=n+k
        A=[P.id(('a',k,i)) for i in range(g)]; B=[P.id(('b',k,i)) for i in range(g)]
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(g):
            for j in range(i+1): cl.append([-A[i],-B[j],NK[k]])
        for i in range(g): cl.append([-NK[k],-A[i],B[i]])
        t=P.id(('t',k)); cl.append([-NK[k],-t])
        for x in X:
            av=P.id(('A',k,x)); bv=P.id(('B',k,x))
            for i in range(g):
                addc([-A[i], lit(i,x,False), av]); addc([-A[i], lit(i,x,True), -av])
                addc([-B[i], lit(i,x,False), bv]); addc([-B[i], lit(i,x,True), -bv])
            v=P.id(('v',g,x))
            cl.append([-t,-v,av]); cl.append([-t,-v,bv]); cl.append([-t,v,-av,-bv])
            cl.append([t,NK[k],v,-av]); cl.append([t,NK[k],v,-bv]); cl.append([t,NK[k],-v,av,bv])
            cl.append([-NK[k],v,av]); cl.append([-NK[k],-v,-av])
            if h0 and x==X[0]: cl.append([-NK[k],v])
    for w,S in enumerate(sets):
        Ow=[P.id(('o',w,k)) for k in range(s)]
        cl.extend(CardEnc.equals(Ow,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for k in range(s):
            cl.append([-Ow[k],-NK[k]])
            for x in X: addc([-Ow[k], lit(n+k,x,any(x[u] for u in S))])
    for k in range(s-1):
        g=n+k
        for i in range(g):
            for j in range(i): cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,j))])
            for a1 in range(i+1):
                for a2 in range(a1): cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,i)),-P.id(('a',k,a1)),-P.id(('a',k+1,a2))])
    for k in range(s):
        g=n+k
        cl.append([P.id(('a',k2,g)) for k2 in range(k+1,s)]+[P.id(('b',k2,g)) for k2 in range(k+1,s)]+[P.id(('o',w,k)) for w in range(len(sets))])
    if readcap is not None:
        for v in range(n):
            d=sum(v in S for S in sets)
            if d==0 or (capvars is not None and v not in capvars): continue
            R=[]
            for k in range(s):
                r=P.id(('r',v,k)); R.append(r)
                cl.append([-P.id(('a',k,v)),r]); cl.append([-P.id(('b',k,v)),r])
            cl.extend(CardEnc.atmost(R,max(1,d-readcap),vpool=P,encoding=EncType.seqcounter).clauses)
    return P,cl
def extract(P,model,n,sets,s):
    ms=set(l for l in model if l>0)
    gates=[]
    for k in range(s):
        g=n+k
        a=[i for i in range(g) if P.id(('a',k,i)) in ms][0]; b=[i for i in range(g) if P.id(('b',k,i)) in ms][0]
        if P.id(('n',k)) in ms: gates.append(['not',a])
        else: gates.append(['and' if P.id(('t',k)) in ms else 'or',a,b])
    outs=[[n+k for k in range(s) if P.id(('o',w,k)) in ms][0] for w in range(len(sets))]
    return dict(n=n,sets=[list(S) for S in sets],gates=gates,outs=outs)
def solve(n,sets,s,tmax=270,block=0,**kw):
    t0=time.time(); P,cl=build(n,sets,s,**kw)
    sv=Cadical153(bootstrap_with=cl)
    import threading
    tm=threading.Timer(tmax,lambda: sv.interrupt()); tm.start()
    res=sv.solve_limited(expect_interrupt=True); tm.cancel()
    out=None
    if res: out=extract(P,sv.get_model(),n,sets,s)
    return res,out,time.time()-t0,len(cl)
SYS={'core8':(8,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7]]),
     'fano':(7,[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]]),
     'k4':(4,[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]]),
     'pasch':(6,[[0,1,2],[0,3,4],[1,3,5],[2,4,5]]),
     'c7':(7,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4]]),
    }
if __name__=='__main__':
    name=sys.argv[1]; s=int(sys.argv[2]); cap=None if sys.argv[3]=='-' else int(sys.argv[3]); nn=int(sys.argv[4]) if len(sys.argv)>4 else 1
    n,sets=SYS[name]
    res,out,t,ncl=solve(n,sets,s,readcap=cap,nnot=nn)
    print(name,'s',s,'base',sum(len(S)-1 for S in sets),'readcap',cap,'nnot',nn,'clauses',ncl,'result',res,'sec %.1f'%t,flush=True)
    if out: open(f'gen_{name}_{s}_{cap}_{nn}.json','w').write(json.dumps(out)); print(json.dumps(out))
