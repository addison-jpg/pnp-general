import sys,json,itertools,time
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
def build(n,sets,s,nots=0,maxcnt=None,extra=None):
    pool=IDPool();cl=[]
    M=1<<n;X=range(M)
    A=[[int(any(x>>u&1 for u in S)) for x in X] for S in sets]
    W=n+s
    def t(k,x): return pool.id(('t',k,x))
    # inputs fixed
    for v in range(n):
        for x in X: cl.append([t(v,x)] if x>>v&1 else [-t(v,x)])
    nvars=[]
    for k in range(n,W):
        ys=[]
        for i in range(k):
            for j in range(i+1,k):
                for op in ('and','or'):
                    y=pool.id(('y',k,i,j,op));ys.append(y)
                    for x in X:
                        a,b,c=t(i,x),t(j,x),t(k,x)
                        if op=='and': cl+= [[-y,-c,a],[-y,-c,b],[-y,c,-a,-b]]
                        else: cl+= [[-y,c,-a],[-y,c,-b],[-y,-c,a,b]]
            if nots:
                y=pool.id(('y',k,i,'not'));ys.append(y);nvars.append(y)
                for x in X: cl+=[[-y,-t(k,x),-t(i,x)],[-y,t(k,x),t(i,x)]]
        cl.append(ys)
        cl+=CardEnc.atmost(ys,1,vpool=pool,encoding=EncType.seqcounter).clauses
    if nots and len(nvars)>1: cl+=CardEnc.atmost(nvars,nots,vpool=pool,encoding=EncType.seqcounter).clauses
    for w,S in enumerate(sets):
        os=[pool.id(('o',w,k)) for k in range(n,W)]
        cl.append(os)
        for k in range(n,W):
            o=pool.id(('o',w,k))
            for x in X: cl.append([-o, t(k,x) if A[w][x] else -t(k,x)])
    big=[w for w,S in enumerate(sets) if len(S)>=2]
    base=sum(len(sets[w])-1 for w in big)
    js=[]
    for k in range(n,W):
        j=pool.id(('j',k));js.append(j);qs=[]
        for a,b in itertools.combinations(big,2):
            qL=pool.id(('qL',k,a,b));qU=pool.id(('qU',k,a,b));qs+=[qL,qU]
            for x in X:
                if not(A[a][x] and A[b][x]): cl.append([-qL,-t(k,x)])
                if A[a][x] or A[b][x]: cl.append([-qU,t(k,x)])
        cl.append([-j]+qs)
    if maxcnt is None: maxcnt=base-1
    # number of non-J gates <= maxcnt  <=> number of j >= s-maxcnt
    cl+=CardEnc.atleast(js,s-maxcnt,vpool=pool,encoding=EncType.seqcounter).clauses
    return pool,cl,base
def decode(pool,model,n,s,sets,nots):
    m=set(v for v in model if v>0);G=[]
    for k in range(n,n+s):
        for i in range(k):
            if nots and pool.id(('y',k,i,'not')) in m: G.append(['not',i])
            for j in range(i+1,k):
                for op in ('and','or'):
                    if pool.id(('y',k,i,j,op)) in m: G.append([op,i,j])
    outs=[next(k for k in range(n,n+s) if pool.id(('o',w,k)) in m) for w in range(len(sets))]
    return dict(n=n,sets=sets,gates=G,outs=outs)
if __name__=='__main__':
    n=int(sys.argv[1]);sets=json.loads(sys.argv[2]);s=int(sys.argv[3]);nots=int(sys.argv[4])
    mc=int(sys.argv[5]) if len(sys.argv)>5 else None
    t0=time.time();pool,cl,base=build(n,sets,s,nots,mc)
    with Solver('cadical153',bootstrap_with=cl) as S:
        r=S.solve()
        print('n',n,'sets',sets,'s',s,'nots',nots,'base',base,'maxcnt',mc if mc is not None else base-1,'SAT' if r else 'UNSAT',round(time.time()-t0,1),flush=True)
        if r:
            c=decode(pool,S.get_model(),n,s,sets,nots);print(json.dumps(c))
