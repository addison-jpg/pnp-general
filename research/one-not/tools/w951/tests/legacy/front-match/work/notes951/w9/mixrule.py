# Fixed averaging rule: each set uses canonical (hallcheck.canon) with prob a and R* (rstar) with prob 1-a.
# LP: within each system spread d_w*lam units, <= lam per gate; minimise max gate load. Rule works iff L <= 1.
import sys, os, json
H=os.path.dirname(os.path.abspath(__file__))
for d in ('../chk','../w8b','../w8'): sys.path.insert(0, os.path.join(H,d))
_a=sys.argv; sys.argv=[_a[0]]
import contextlib, io
with contextlib.redirect_stdout(io.StringIO()): from hallcheck import canon
sys.argv=_a
from rstar import rstar
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def fixedlp(Dlist, lams, dem):
    # Dlist[w] = list of counted sets, lams[w] = list of fixed weights
    var={'L':0}; rows_eq=[]; rows_ub=[]
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    for w,(Ds,ls) in enumerate(zip(Dlist,lams)):
        for j,(D,l) in enumerate(zip(Ds,ls)):
            if l==0: continue
            if len(D)<dem[w]: return float('inf')
            rows_eq.append(({v(('y',w,j,g)):1 for g in D}, dem[w]*l))
    gates=sorted({k[3] for k in var if k!='L'})
    for g in gates:
        r={i:1 for k,i in var.items() if k!='L' and k[3]==g}; r[0]=-1; rows_ub.append((r,0))
    nv=len(var)
    def mat(rows):
        A=lil_matrix((len(rows),nv)); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    Ae,be=mat(rows_eq); Au,bu=mat(rows_ub)
    bounds=[(0,None)]+[None]*(nv-1)
    for k,i in var.items():
        if k!='L': bounds[i]=(0,lams[k[1]][k[2]])
    cst=np.zeros(nv); cst[0]=1
    r=linprog(cst,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=bounds,method='highs')
    return r.fun if r.status==0 else float('inf')
def mix(c, a=0.5):
    dem=[len(s)-1 for s in c['sets']]
    Dc=canon(c); Dr=rstar(c)
    return fixedlp([[x,y] for x,y in zip(Dc,Dr)], [[a,1-a]]*len(dem), dem)
if __name__=='__main__':
    a=float(sys.argv[2]) if len(sys.argv)>2 else 0.5
    f=sys.argv[1]; cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    from collections import Counter; h=Counter(); worst=(0,None)
    for i,c in enumerate(cs):
        L=mix(c,a); h[round(L,3)]+=1
        if L>worst[0]: worst=(L,i)
    print(f,'a',a,'n',len(cs),'worst',round(worst[0],4),'at',worst[1],'hist',sorted(h.items())[-5:])
