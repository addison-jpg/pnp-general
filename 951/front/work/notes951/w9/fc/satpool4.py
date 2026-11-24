# Exhaustive SAT: is there a correct one-NOT circuit (h(0)=0) of size s for the given triples such that ALL merge gates
# (any legal system: any z, any fat atoms, K=all) of the triples in FAM lie in a pool of <= |FAM|-1 gates?  (= MatchG/FracMatch counterexample)
import sys, itertools, json, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
def build(n, sets, s, fam, poolsize, nset=True):
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
    cl.extend(CardEnc.equals(NK,1,vpool=P,encoding=EncType.seqcounter).clauses)
    for k in range(s):
        g=n+k
        A=[P.id(('a',k,i)) for i in range(g)]; B=[P.id(('b',k,i)) for i in range(g)]
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(g):
            for j in range(i+1): cl.append([-A[i],-B[j],NK[k]] if j<i else [-A[i],-B[j],NK[k]])   # a<b unless NOT
        for i in range(g): cl.append([-NK[k],-A[i],B[i]])       # NOT: b=a
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
            # global N value at x
            nx=P.id(('N',x)); cl.append([-NK[k],-v,nx]); cl.append([-NK[k],v,-nx])
    cl.append([P.id(('N',X[0]))])   # h(0)=0
    O={}
    for w in range(len(sets)):
        for k in range(s): P.id(('o',w,k))
    for w,S in enumerate(sets):
        Ow=[P.id(('o',w,k)) for k in range(s)]; O[w]=Ow
        cl.extend(CardEnc.equals(Ow,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for k in range(s):
            cl.append([-Ow[k],-NK[k]])
            for x in X: addc([-Ow[k], lit(n+k,x,any(x[u] for u in S))])
    # symmetry breaking: colex order of (b,a); every gate read or output
    for k in range(s-1):
        g=n+k
        for i in range(g):
            for j in range(i):          # b_k=i, b_{k+1}=j<i forbidden
                cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,j))])
            for a1 in range(i+1):
                for a2 in range(a1):    # same b, a decreasing forbidden
                    cl.append([-P.id(('b',k,i)),-P.id(('b',k+1,i)),-P.id(('a',k,a1)),-P.id(('a',k+1,a2))])
    for k in range(s):
        g=n+k
        cl.append([P.id(('a',k2,g)) for k2 in range(k+1,s)]+[P.id(('b',k2,g)) for k2 in range(k+1,s)]+[P.id(('o',w,k)) for w in range(len(sets))])
    PL=[P.id(('P',k)) for k in range(s)]
    cl.extend(CardEnc.atmost(PL,poolsize,vpool=P,encoding=EncType.seqcounter).clauses)
    for w in fam:
        S=sets[w]; rest=[v for v in range(n) if v not in S]
        for zm in itertools.product([0,1],repeat=len(rest)):
            z=[0]*n
            for v,b in zip(rest,zm): z[v]=b
            z=tuple(z); ones=[v for v in rest if z[v]]
            subs=[T for r in range(len(ones)+1) for T in itertools.combinations(ones,r)]
            def atom(u,T):
                p=[0]*n; p[u]=1
                for v in T: p[v]=1
                return tuple(p)
            for u,v2 in itertools.combinations(S,2):
                for T1 in subs:
                    pu=atom(u,T1)
                    for T2 in subs:
                        pv=atom(v2,T2)
                        for k in range(s):
                            g=n+k; base=[P.id(('v',g,z)),-P.id(('v',g,pu)),-P.id(('v',g,pv)),PL[k],O[w][k]]
                            cl.append(base+[-P.id(('N',z))]); cl.append(base+[P.id(('N',pu))]); cl.append(base+[P.id(('N',pv))])
    return P,cl,X
def decode(P,M,n,sets,s):
    pos=set(l for l in M if l>0); G=[]
    for k in range(s):
        a=[i for i in range(n+k) if P.id(('a',k,i)) in pos][0]; b=[i for i in range(n+k) if P.id(('b',k,i)) in pos][0]
        if P.id(('n',k)) in pos: G.append(['not',a])
        else: G.append(['and' if P.id(('t',k)) in pos else 'or',a,b])
    outs=[[n+k for k in range(s) if P.id(('o',w,k)) in pos][0] for w in range(len(sets))]
    pool=[n+k for k in range(s) if P.id(('P',k)) in pos]
    return dict(n=n,sets=[list(S) for S in sets],gates=G,outs=outs),pool
SYS={'path':(7,[(0,1,4),(1,2,3),(4,5,6)]),'sun':(7,[(0,1,4),(0,2,5),(0,3,6)]),'tri':(6,[(0,1,2),(2,3,4),(4,5,0)]),
     'pasch':(6,[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]),'fan':(6,[(0,1,2),(0,3,4),(1,3,5)]),'disj':(9,[(0,1,2),(3,4,5),(6,7,8)]),
     'p3':(7,[(0,1,2),(2,3,4),(4,5,6)]),
     'C44':(7,[(0,1,2,3),(0,4,5,6)]),'D44':(8,[(0,1,2,3),(4,5,6,7)]),'A433':(7,[(0,1,2,3),(0,4,5),(1,4,6)]),'F433':(7,[(0,1,2,3),(3,4,5),(5,6,0)])}
if __name__=='__main__':
    name=sys.argv[1]; s=int(sys.argv[2]); secs=float(sys.argv[3]); n,sets=SYS[name]
    fam=[w for w,S in enumerate(sets) if len(S)>=3]; t0=time.time()
    ps=int(sys.argv[4]) if len(sys.argv)>4 else sum(len(sets[w])-2 for w in fam)-1
    P,cl,X=build(n,sets,s,fam,ps); print('pool<=',ps)
    if len(sys.argv)>5:   # fixed h: list of minterms like 12,45
        mts=[[int(ch) for ch in m] for m in sys.argv[5].split(',')]
        for x in X:
            hx=any(all(x[v] for v in m) for m in mts); cl.append([-P.id(('N',x)) if hx else P.id(('N',x))])
        print('fixed h minterms',mts); print(name,'s',s,'clauses',len(cl),'build',round(time.time()-t0,1),flush=True)
    sol=Cadical153(bootstrap_with=cl)
    import threading
    tm=threading.Timer(secs,lambda: sol.interrupt()); tm.start()
    r=sol.solve_limited(expect_interrupt=True); tm.cancel()
    print('result',{True:'SAT',False:'UNSAT',None:'TIMEOUT'}[r],'sec',round(time.time()-t0,1))
    if r:
        c,pool=decode(P,sol.get_model(),n,sets,s); print('pool',pool); print(json.dumps(c))
        json.dump(c,open('satpool_%s_%d.json'%(name,s),'w'))
