# SAT search for a correct one-NOT circuit violating TWO-WORLD HALL with F_c=F_r=all (|U| <= base-1 - slack),
# Dc computed over ALL gates (superset of cone Dc => violation transfers), canonical Q = smallest h-Good superset.
import sys, itertools, json, time
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
def build(n, sets, s, pnot, K, extra=None):
    P=IDPool(); cl=[]
    X=list(itertools.product([0,1],repeat=n)); X=[tuple(x) for x in X]; idx={x:i for i,x in enumerate(X)}
    W=n+s
    def val(i,x):
        if i<n: return None
        return P.id(('v',i,x))
    def lit(i,x,pos=True):
        # returns literal or True/False for inputs
        if i<n: return bool(x[i])==pos
        return P.id(('v',i,x)) if pos else -P.id(('v',i,x))
    def addc(c):
        out=[]
        for l in c:
            if l is True: return
            if l is False: continue
            out.append(l)
        cl.append(out)
    hsel=[P.id(('h',i)) for i in range(pnot+n)]
    cl.extend(CardEnc.equals([P.id(('h',i)) for i in range(n+pnot)],1,vpool=P,encoding=EncType.seqcounter).clauses)
    for k in range(s):
        g=n+k
        if k==pnot:
            for i in range(n+pnot):
                for x in X:
                    addc([-P.id(('h',i)), lit(i,x,True), lit(g,x,True)]); addc([-P.id(('h',i)), lit(i,x,False), lit(g,x,False)])
            continue
        A=[P.id(('a',k,i)) for i in range(g)]; B=[P.id(('b',k,i)) for i in range(g)]
        cl.extend(CardEnc.equals(A,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.extend(CardEnc.equals(B,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for i in range(g):   # a < b
            for j in range(i+1):
                cl.append([-A[i] if False else -P.id(('a',k,i)), -P.id(('b',k,j))]) if j<=i else None
        t=P.id(('t',k))  # t=1 AND, 0 OR
        for x in X:
            av=P.id(('A',k,x)); bv=P.id(('B',k,x))
            for i in range(g):
                addc([-A[i], lit(i,x,False), av]); addc([-A[i], lit(i,x,True), -av])
                addc([-B[i], lit(i,x,False), bv]); addc([-B[i], lit(i,x,True), -bv])
            v=P.id(('v',g,x))
            # AND
            addc([-t,-v,av]); addc([-t,-v,bv]); addc([-t,v,-av,-bv])
            # OR
            addc([t,v,-av]); addc([t,v,-bv]); addc([t,-v,av,bv])
    # h value
    def hv(x,pos=True):
        return -P.id(('v',n+pnot,x)) if pos else P.id(('v',n+pnot,x))   # h = not N
    # outputs
    m=len(sets)
    for w,S in enumerate(sets):
        O=[P.id(('o',w,k)) for k in range(s)]
        cl.extend(CardEnc.equals(O,1,vpool=P,encoding=EncType.seqcounter).clauses)
        cl.append([-P.id(('o',w,pnot))])
        for k in range(s):
            for x in X:
                f=any(x[u] for u in S); addc([-O[k], lit(n+k,x,f)])
    def z(Z): return tuple(0 if v in Z else 1 for v in range(n))
    def e(u,base=None):
        b=list(base) if base else [0]*n; b[u]=1; return tuple(b)
    U=[P.id(('U',k)) for k in range(s)]
    for w,S in enumerate(sets):
        Sset=set(S)
        # hard
        addc([hv(z(Sset),True)])
        sup=[]; rest=[v for v in range(n) if v not in Sset]
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r): sup.append(Sset|set(ex))
        q=[P.id(('q',w,j)) for j in range(len(sup))]
        cl.extend(CardEnc.equals(q,1,vpool=P,encoding=EncType.seqcounter).clauses)
        for j,Q in enumerate(sup):
            addc([-q[j], hv(z(Q),False)])
            for jj in range(j): addc([-q[j], hv(z(sup[jj]),True)])
        for k in range(s):
            g=n+k
            for u,v in itertools.combinations(S,2):
                for j,Q in enumerate(sup):
                    addc([-q[j], lit(g,z(Q),True), lit(g,e(u),False), lit(g,e(v),False), U[k]])
                zs=z(Sset)
                addc([lit(g,zs,True), lit(g,e(u,zs),False), lit(g,e(v,zs),False), U[k]])
    base=sum(len(S)-1 for S in sets)
    cl.extend(CardEnc.atmost(U,K,vpool=P,encoding=EncType.seqcounter).clauses)
    # every gate read or output (helps prune)
    for k in range(s):
        if k==pnot: rd=[P.id(('a',kk,n+k)) for kk in range(k+1,s) if kk!=pnot]+[P.id(('b',kk,n+k)) for kk in range(k+1,s) if kk!=pnot]+[P.id(('h',n+k))] if False else None
    return P,cl,X
def decode(P,model,n,s,sets,pnot):
    M=set(l for l in model if l>0); G=[]
    for k in range(s):
        g=n+k
        if k==pnot:
            G.append(['not',[i for i in range(n+pnot) if P.id(('h',i)) in M][0]]); continue
        a=[i for i in range(g) if P.id(('a',k,i)) in M][0]; b=[i for i in range(g) if P.id(('b',k,i)) in M][0]
        G.append(['and' if P.id(('t',k)) in M else 'or',a,b])
    outs=[n+[k for k in range(s) if P.id(('o',w,k)) in M][0] for w in range(len(sets))]
    return dict(n=n,sets=sets,gates=G,outs=outs)
if __name__=='__main__':
    n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); s=int(sys.argv[3]); pnot=int(sys.argv[4])
    base=sum(len(S)-1 for S in sets); K=int(sys.argv[5]) if len(sys.argv)>5 else base-1
    t=time.time(); P,cl,X=build(n,sets,s,pnot,K); print('vars',P.top,'clauses',len(cl),'build',round(time.time()-t,1),flush=True)
    S=Cadical153(bootstrap_with=cl); r=S.solve(); print('SAT' if r else 'UNSAT', round(time.time()-t,1))
    if r:
        c=decode(P,S.get_model(),n,s,sets,pnot); print(json.dumps(c))
