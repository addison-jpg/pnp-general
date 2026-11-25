# Residual ("private classes reserved") FracMatch LP + duals, and world-restricted duals.
import sys, json, os, itertools, pickle
H=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,H)
import dualp
from dualp import Dual, roles, evalN
from allsys import menus
def tables(c):
    n,G=c['n'],c['gates']; T=[[] for _ in range(n+len(G))]
    for x in itertools.product([0,1],repeat=n):
        w=evalN(n,G,list(x))
        for i,v in enumerate(w): T[i].append(v)
    return T
def private(c):
    n,G,S=c['n'],c['gates'],c['sets']; T=tables(c); X=list(itertools.product([0,1],repeat=n))
    OR=[[int(any(x[v] for v in s)) for x in X] for s in S]
    unit=[evalN(n,G,[int(v==u) for v in range(n)]) for u in range(n)]
    le=lambda a,b: all(p<=q for p,q in zip(a,b))
    Dc=[];Pc=[]
    for i,s in enumerate(S):
        Dc.append({g for g in range(n,n+len(G)) if le(T[g],OR[i]) and sum(unit[u][g] for u in s)>=2})
        Pc.append({g for g in range(n,n+len(G)) if le(OR[i],T[g]) and not all(T[g]) and not any(le(OR[j],T[g]) for j in range(len(S)) if j!=i)})
    return Dc,Pc
def full(c,cone=False):
    """menu items with witness: list per set of (cnt sorted, z, hz)"""
    n,G=c['n'],c['gates']; nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=G[nw-n][1]
    out=[]
    for m in menus(c,cone):
        out.append([(sorted(C),z,evalN(n,G,list(z))[h]) for C,(z,at) in sorted(m.items(),key=lambda kv:sorted(kv[0]))])
    return out
def lpdual(M,dem):
    import random
    D=Dual(M,dem); L,pi,mu=D.solve(); pif,muf=D.flat(L); return L,pif,muf,D
def fmt(pi,R,cntby=None):
    if not pi: return ''
    mn=min(pi.values()); return ' '.join('g%d:%.3g[%s%s]'%(g,pi[g]/mn,R[g]['op'],','+'/'.join(R[g]['tags']) if R[g]['tags'] else '') for g in sorted(pi))
def run(c,name,verbose=True):
    F=full(c); dem=[len(s)-1 for s in c['sets']]; R=roles(c); Dc,Pc=private(c)
    Pi=[Dc[i]|Pc[i] for i in range(len(dem))]; allP=set().union(*Pi)
    M=[[C for C,z,hz in m] for m in F]
    L,pi,mu,_=lpdual(M,dem)
    m_i=[max(len(Pi[i]&set(C)) for C in M[i]) for i in range(len(dem))]
    short=[i for i in range(len(dem)) if m_i[i]<dem[i]]
    res=dict(name=name,L=L,pi=pi,m=m_i,short=short,dem=dem)
    # residual LP
    Mr=[];demr=[]
    # per item residual demand differs -> model each set with common demand by padding: use item-specific demand via dummy free gates
    # trick: add (|Pi_i ∩ C| capped at d) private dummy gates per set so demand stays d_i but Pi gates are replaced by set-private dummies
    for i,m in enumerate(M):
        items=[]
        for C in m:
            k=min(dem[i],len(Pi[i]&set(C)))
            items.append([g for g in C if g not in allP]+[('priv',i,t) for t in range(k)])
        Mr.append(items)
    # dummies must not carry price: solve dual with pi restricted to real gates => do it by giving dummies capacity (free): remove them and lower demand per item
    Lr,pir=resid_lp(Mr,dem)
    res.update(Lres=Lr,pires=pir)
    if verbose:
        print('=== %s sets=%s L*=%.4f  m_i=%s d_i=%s short=%s  L_res=%s'%(name,c['sets'],L,m_i,dem,short,None if Lr is None else round(Lr,4)))
        print('   pi(flat):',fmt(pi,R)); 
        if pir: print('   pi_res :',fmt(pir,R))
    return res
def resid_lp(Mr,dem):
    """min L s.t. real gates load<=L, dummy gates load<=1 (free). Returns L, dual prices on real gates (HiGHS marginals)."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import lil_matrix
    var={'L':0}
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    sysl=[(w,j,C) for w,m in enumerate(Mr) for j,C in enumerate(m)]
    for w,j,C in sysl:
        v(('lam',w,j))
        for g in C: v(('y',w,j,g))
    gates=sorted({g for _,_,C in sysl for g in C if not isinstance(g,tuple)})
    eq=[];ub=[];grow={}
    for w,m in enumerate(Mr): eq.append(({v(('lam',w,j)):1 for j in range(len(m))},1))
    for w,j,C in sysl:
        r={v(('y',w,j,g)):1 for g in C}; r[v(('lam',w,j))]=-dem[w]; eq.append((r,0))
        for g in C: ub.append(({v(('y',w,j,g)):1, v(('lam',w,j)):-1},0))
    for g in gates:
        r={v(('y',w,j,g)):1 for w,j,C in sysl if g in C}; r[0]=-1; ub.append((r,0)); grow[g]=len(ub)-1
    def mat(rows):
        A=lil_matrix((len(rows),len(var))); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    Ae,be=mat(eq); Au,bu=mat(ub); cost=np.zeros(len(var)); cost[0]=1
    res=linprog(cost,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=[(0,None)]*len(var),method='highs')
    if res.status!=0: return None,None
    pi={g:-res.ineqlin.marginals[grow[g]] for g in gates if -res.ineqlin.marginals[grow[g]]>1e-9}
    return res.fun,pi
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        for i,c in enumerate(cs): run(c,os.path.basename(f)+('#%d'%i if len(cs)>1 else ''))
