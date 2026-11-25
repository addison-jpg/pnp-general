# S-repay-V1 for any number of sets: integral choice of one lifted class per set (full menu of analyze.menu, minimal+maximal classes);
# minimise waste = |U| - maxflow  (V1 slack = (s-1-base) - waste), and separately maximise flow (min deficiency).
import sys, numpy as np, collections, json
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
sys.argv=sys.argv[:1] if __name__!='__main__' else sys.argv
from analyze import *
def v1(T,menus,dem,mode='waste'):
    G=len(T.GL); m=len(dem)
    opts=[list(mn.keys()) for mn in menus]
    var={}
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    for w in range(m):
        for j in range(len(opts[w])): v(('l',w,j))
    for g in range(G): v(('u',g))
    for w in range(m):
        for g in range(G):
            if any(o>>g&1 for o in opts[w]): v(('y',w,g))
    rows=[];lo=[];hi=[]
    def row(d,l,h): rows.append(d); lo.append(l); hi.append(h)
    for w in range(m): row({v(('l',w,j)):1 for j in range(len(opts[w]))},1,1)
    for w in range(m):
        for g in range(G):
            js=[j for j,o in enumerate(opts[w]) if o>>g&1]
            if not js: continue
            d={v(('l',w,j)):-1 for j in js}; d2=dict(d)
            d[v(('u',g))]=1; row(d,0,np.inf)                 # u_g >= [chosen class of w contains g]
            d2[v(('y',w,g))]=1; row(d2,-np.inf,0)            # y_wg <= [chosen class contains g]
        row({v(('y',w,g)):1 for g in range(G) if ('y',w,g) in var},-np.inf,dem[w])
    for g in range(G):
        d={v(('y',w,g)):1 for w in range(m) if ('y',w,g) in var}
        if d: row(d,-np.inf,1)
    A=lil_matrix((len(rows),len(var)))
    for i,d in enumerate(rows):
        for k,a in d.items(): A[i,k]=a
    cost=np.zeros(len(var)); integ=np.zeros(len(var))
    for k,i in var.items():
        if k[0]=='l': integ[i]=1
        if mode=='waste':
            if k[0]=='u': cost[i]=1
            if k[0]=='y': cost[i]=-1
        else:
            if k[0]=='y': cost[i]=-1
    res=milp(cost,constraints=LinearConstraint(A.tocsr(),lo,hi),integrality=integ,bounds=Bounds(0,1),options=dict(time_limit=120))
    return res.fun, res.status
def run(name,c):
    r,T,menus=analyze(name,c,verbose=False,lpdo=True)
    dem=[len(s)-1 for s in c['sets']]; base=sum(dem); sM=len(T.GL)
    waste,st1=v1(T,menus,dem,'waste'); flow,st2=v1(T,menus,dem,'flow')
    r['V1waste']=round(waste,3); r['V1slack_multi']=round(sM-base-waste,3); r['mindef']=round(base+flow,3)
    return r
if __name__=='__main__':
    from bt import allcirc
    out=[]
    for name,c in allcirc():
        if c['n']>9: continue
        r=run(name,c); out.append((r['V1slack_multi'],r['mindef'],r['Lmax'],name,r['s'],r['base']))
    out.sort(); print(len(out)); print(out[:8])
    print('mindef>0:',[(o[3],o[1]) for o in out if o[1]>1e-6][:20])
