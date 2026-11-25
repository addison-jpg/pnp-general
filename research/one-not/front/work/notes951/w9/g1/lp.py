import sys, itertools, numpy as np
from scipy.optimize import linprog
from g1lib import *
def family(c,T,kinds='ABCDE'):
    n=c['n']; S=c['sets']; m=len(S); fam=[]
    used=[v for v in range(n) if deg(c,v)]
    if 'A' in kinds:
        for v in used: fam.append(('z%d'%v,)+sub(c,T,Z=[v]))
    if 'B' in kinds:
        for v in used: fam.append(('o%d'%v,)+sub(c,T,O=[v]))
    if 'C' in kinds and m>1:
        for w in range(m): fam.append(('d%d'%w,)+sub(c,T,keep=[x for x in range(m) if x!=w]))
    if 'D' in kinds:
        for u,v in itertools.combinations(used,2): fam.append(('z%d,%d'%(u,v),)+sub(c,T,Z=[u,v]))
    if 'E' in kinds:
        for w in range(m): fam.append(('k%d'%w,)+sub(c,T,Z=[v for v in range(n) if v not in S[w]],keep=[w]))
    if 'F' in kinds:
        for u,v in itertools.combinations(used,2):
            fam.append(('z%do%d'%(u,v),)+sub(c,T,Z=[u],O=[v])); fam.append(('z%do%d'%(v,u),)+sub(c,T,Z=[v],O=[u]))
    if 'G' in kinds:   # zero a whole set / zero all but star...
        for w in range(m): fam.append(('Z%d'%w,)+sub(c,T,Z=S[w]))
    return [f for f in fam if f[2]>0]
def lpval(c,fam,ret=False):
    n=c['n']; s=len(c['gates'])
    if not fam: return 0.0
    A=np.zeros((s,len(fam)))
    for j,(nm,al,b) in enumerate(fam):
        for g in al: A[g-n,j]=1
    r=linprog(-np.array([f[2] for f in fam],float),A_ub=A,b_ub=np.ones(s),bounds=(0,None),method='highs')
    if ret: return -r.fun,r
    return -r.fun
if __name__=='__main__':
    kindsets=sys.argv[1].split(',')
    for f in sys.argv[2:]:
        cs=[c for c in load(f) if c['n']<=10]
        res=[]
        for c in cs:
            T=tts(c); b=base(c['sets']); s=len(c['gates'])
            row=[b,s]
            for ks in kindsets:
                row.append(lpval(c,family(c,T,ks)))
            res.append(row)
        if len(res)<=3:
            for r in res: print(f.split('/')[-1],'base',r[0],'s',r[1],dict(zip(kindsets,[round(x,3) for x in r[2:]])))
        else:
            for i,ks in enumerate(kindsets):
                print(f.split('/')[-1],len(res),ks,'min V-base %.3f'%min(r[2+i]-r[0] for r in res),'#V<base',sum(r[2+i]<r[0]-1e-7 for r in res),'min V/base %.3f'%min(r[2+i]/r[0] for r in res))
