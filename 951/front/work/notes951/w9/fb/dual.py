# FracMatch LP with dual prices. L* = max_pi sum_w min_j cheap_{d_w}(pi, C_wj) / sum pi.
import sys, json, os
H=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(H,'..','..','w8')); sys.path.insert(0, os.path.join(H,'..'))
from allsys import menus
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def lp(M, dem, cap=None, fixed=None):
    """M[w] = list of counted sets. cap[g]: capacity multiplier (default 1). returns L, pi(dict), mu(list), lam"""
    var={'L':0}
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    sysl=[(w,j,sorted(C)) for w,m in enumerate(M) for j,C in enumerate(m)]
    for w,j,C in sysl:
        v(('lam',w,j))
        for g in C: v(('y',w,j,g))
    gates=sorted({g for _,_,C in sysl for g in C})
    eq=[];ub=[]
    for w,m in enumerate(M): eq.append(({v(('lam',w,j)):1 for j in range(len(m))},1))
    for w,j,C in sysl:
        r={v(('y',w,j,g)):1 for g in C}; r[v(('lam',w,j))]=-dem[w]; eq.append((r,0))
        for g in C: ub.append(({v(('y',w,j,g)):1, v(('lam',w,j)):-1},0))
    grow={}
    for g in gates:
        r={v(('y',w,j,g)):1 for w,j,C in sysl if g in C}
        if fixed and g in fixed: ub.append((r,fixed[g]))
        else: r[0]=-(1 if cap is None else cap.get(g,1))
        if not (fixed and g in fixed): ub.append((r,0))
        grow[g]=len(ub)-1
    def mat(rows):
        A=lil_matrix((len(rows),len(var))); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    Ae,be=mat(eq); Au,bu=mat(ub); cost=np.zeros(len(var)); cost[0]=1
    res=linprog(cost,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=[(0,None)]*len(var),method='highs')
    if res.status!=0: return None
    pi={g:-res.ineqlin.marginals[grow[g]] for g in gates if -res.ineqlin.marginals[grow[g]]>1e-9}
    mu=[res.eqlin.marginals[w] for w in range(len(M))]
    lam={(k[1],k[2]):res.x[i] for k,i in var.items() if k!='L' and k[0]=='lam' and res.x[i]>1e-9}
    load={g:sum(res.x[var[('y',w,j,g)]] for w,j,C in sysl if g in C) for g in gates}
    return res.fun,pi,mu,lam,load
def desc(c):
    """symbolic description of gates"""
    n=c['n']; nm=['x%d'%i for i in range(n)]
    for k,g in enumerate(c['gates']):
        if g[0]=='not': nm.append('N')
        else: nm.append('g%d'%(n+k))
    return nm
def cheap(pi,C,d): return sum(sorted(pi.get(g,0) for g in C)[:d])
if __name__=='__main__':
    f=sys.argv[1]; cone=len(sys.argv)>2
    cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    for c in cs[:3]:
        M=menus(c,cone); M=[list(m) for m in M]; dem=[len(s)-1 for s in c['sets']]
        L,pi,mu,lam,load=lp(M,dem)
        print(f,'L*',round(L,5),'menus',[len(m) for m in M],'pi',{g:round(p,3) for g,p in pi.items()},'mu',[round(x,3) for x in mu])
        for (w,j),x in sorted(lam.items()): print('  set',w,c['sets'][w],'lam',round(x,3),'cnt',sorted(M[w][j]))
        for k,g in enumerate(c['gates']): print('   ',c['n']+k,g, 'OUT' if c['n']+k in c['outs'] else '')
