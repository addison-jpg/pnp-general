# Dual prices for FracMatch.  L* = max_{pi>=0, sum pi=1} sum_w min_j cheap_{d_w}(pi, C_wj)
# explicit dual LP (cheap_d(pi,C) = max_tau d*tau - sum_g (tau-pi_g)^+), then tie-breaks among optimal duals.
import sys, json, os, pickle, itertools, hashlib
H=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,H)
from allsys import menus
from verify import evalN
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
def get_menus(c, cone=False):
    key=hashlib.md5((json.dumps(c,sort_keys=True)+str(cone)).encode()).hexdigest()
    p=os.path.join(H,'out','menu_'+key+'.pkl')
    if os.path.exists(p): return pickle.load(open(p,'rb'))
    M=[sorted(sorted(x) for x in m) for m in menus(c,cone)]
    pickle.dump(M,open(p,'wb')); return M
def cheap(pi,C,d): return sum(sorted(pi.get(g,0) for g in C)[:d])
def ratio(pi,M,dem):
    return sum(min(cheap(pi,C,d) for C in m) for m,d in zip(M,dem))/sum(pi.values())
class Dual:
    def __init__(s,M,dem):
        s.M,s.dem=M,dem; s.var={}
        s.gates=sorted({g for m in M for C in m for g in C})
        for g in s.gates: s.v(('pi',g))
        for w in range(len(M)): s.v(('mu',w))
        s.ub=[]
        for w,m in enumerate(M):
            for j,C in enumerate(m):
                t=s.v(('tau',w,j)); r={s.v(('mu',w)):1, t:-dem[w]}
                for g in C:
                    rho=s.v(('rho',w,j,g)); r[rho]=1
                    s.ub.append(({t:1,rho:-1,s.v(('pi',g)):-1},0))
                s.ub.append((r,0))
        s.nv=len(s.var)
    def v(s,k):
        if k not in s.var: s.var[k]=len(s.var)
        return s.var[k]
    def mat(s,rows,nv=None):
        nv=nv or s.nv
        A=lil_matrix((len(rows),nv)); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    def solve(s, obj=None, extra_ub=(), extra_eq=(), integer_scale=None):
        """max sum mu s.t. sum pi = 1 (default)."""
        cost=np.zeros(s.nv)
        if obj is None:
            for w in range(len(s.M)): cost[s.var[('mu',w)]]=-1
        else:
            for k,a in obj.items(): cost[s.var[k]]=a
        Au,bu=s.mat(s.ub+list(extra_ub)); Ae,be=s.mat([({s.var[('pi',g)]:1 for g in s.gates},1)]+list(extra_eq))
        res=linprog(cost,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=[(0,None)]*s.nv,method='highs')
        assert res.status==0,res.message
        pi={g:res.x[s.var[('pi',g)]] for g in s.gates if res.x[s.var[('pi',g)]]>1e-9}
        mu=[res.x[s.var[('mu',w)]] for w in range(len(s.M))]
        return -res.fun if obj is None else res.fun, pi, mu
    def optrow(s,L):  # constraint sum mu >= L
        return ({s.var[('mu',w)]:-1 for w in range(len(s.M))},-L+1e-9)
    def flat(s,L):
        """among optimal duals: minimise max pi (most spread-out), returns pi"""
        k=('mx',); 
        if k not in s.var: s.var[k]=len(s.var); s.nv=len(s.var)
        ex=[s.optrow(L)]+[({s.var[('pi',g)]:1,s.var[k]:-1},0) for g in s.gates]
        _,pi,mu=s.solve(obj={k:1},extra_ub=ex); return pi,mu
    def sparse(s,L,rng,tries=20):
        """heuristic min support among optimal duals: random-weight LPs, keep smallest support"""
        best=None
        for t in range(tries):
            obj={('pi',g):rng.random() for g in s.gates}
            _,pi,mu=s.solve(obj=obj,extra_ub=[s.optrow(L)])
            if best is None or len(pi)<len(best[0]): best=(pi,mu)
        return best
def best01(M,dem,gates,timelimit=60):
    """max over U of [sum_w min_j (d_w-|C_wj \\ U|)^+] - L*|U| is awkward; instead for each size normalisation solve
    max sum_w m_w - theta*|U| by Dinkelbach on theta. MILP vars: u_g in{0,1}, m_w>=0 integer-free, m_w <= b_wj*BIG ... 
    (d-|C\\U|)^+ = max(0, d-|C|+|C∩U|). m_w<=min_j of that: need m_w <= max(0,a_j): binary s_wj: m_w <= a_j + D*(1-s_wj), m_w <= D*s_wj."""
    gi={g:i for i,g in enumerate(gates)}; ng=len(gates); nw=len(M)
    idx=ng+nw; sv={}
    for w,m in enumerate(M):
        for j in range(len(m)): sv[(w,j)]=idx; idx+=1
    rows=[];lo=[];hi=[]
    for w,m in enumerate(M):
        d=dem[w]
        for j,C in enumerate(m):
            r=np.zeros(idx); r[ng+w]=1
            for g in C: r[gi[g]]-=1
            r[sv[(w,j)]]=d; rows.append(r); lo.append(-np.inf); hi.append(d-len(C)+d)
            r=np.zeros(idx); r[ng+w]=1; r[sv[(w,j)]]=-d; rows.append(r); lo.append(-np.inf); hi.append(0)
    r=np.zeros(idx); r[:ng]=1; rows.append(r); lo.append(1); hi.append(np.inf)
    A=np.array(rows); integ=np.ones(idx); integ[ng:ng+nw]=0
    bounds=Bounds(np.zeros(idx),np.concatenate([np.ones(ng),np.array(dem,float),np.ones(idx-ng-nw)]))
    theta=0.0; bestU=None
    for it in range(30):
        cost=np.zeros(idx); cost[:ng]=theta; cost[ng:ng+nw]=-1
        res=milp(cost,constraints=LinearConstraint(A,lo,hi),integrality=integ,bounds=bounds,options={'time_limit':timelimit})
        if res.x is None: break
        U=[g for g in gates if res.x[gi[g]]>.5]; val=sum(res.x[ng:ng+nw])
        if not U: break
        nt=val/len(U)
        if nt<=theta+1e-9: break
        theta=nt; bestU=U
    return theta,bestU
def roles(c):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; ng=len(G)
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=G[nw-n][1]
    down={nw}
    for k,g in enumerate(G):
        if any(j in down for j in g[1:]): down.add(n+k)
    def cone(o):
        seen=set(); st=[o]
        while st:
            i=st.pop()
            if i in seen or i<n: continue
            seen.add(i); st+=G[i-n][1:]
        return seen
    hc=cone(h)|{h}; oc=[cone(o) for o in outs]
    z0=evalN(n,G,[0]*n); unit=[evalN(n,G,[int(v==u) for v in range(n)]) for u in range(n)]
    R={}
    for k,g in enumerate(G):
        i=n+k; t=[]
        if i==nw: t.append('NOT')
        if i==h: t.append('h')
        if i in outs: t+=['OUT%d'%w for w,o in enumerate(outs) if o==i]
        t.append('aboveN' if i in down and i!=nw else ('belowh' if i in hc and i!=h else ('' if i in (nw,h) else 'side')))
        R[i]=dict(op=g[0],ins=g[1:],tags=[x for x in t if x],cones=[w for w in range(len(S)) if i in oc[w]],
                  z0=z0[i],units=[u for u in range(n) if unit[u][i]!=z0[i]])
    return R
def analyse(c,name,cone=False,do01=True,verbose=True):
    import random
    M=get_menus(c,cone); dem=[len(s)-1 for s in c['sets']]
    D=Dual(M,dem); L,pi,mu=D.solve()
    assert abs(ratio(pi,M,dem)-L)<1e-6,(ratio(pi,M,dem),L)
    pif,muf=D.flat(L); pis,mus=D.sparse(L,random.Random(1))
    R=roles(c); n=c['n']
    cntby={g:[w for w,m in enumerate(M) if any(g in C for C in m)] for g in D.gates}
    out=dict(name=name,n=n,s=len(c['gates']),base=sum(dem),sets=c['sets'],L=L,menus=[len(m) for m in M],
             pi_vertex=pi,pi_flat=pif,pi_sparse=pis,mu=mu,mu_flat=muf,mu_sparse=mus)
    if do01:
        th,U=best01(M,dem,D.gates); out['L01']=th; out['U01']=U
    out['roles']={g:R[g] for g in R}; out['cntby']=cntby
    if verbose: show(out,c,M)
    return out
def show(o,c,M):
    R=o['roles']; n=o['n']; dem=[len(s)-1 for s in c['sets']]
    print('=== %s n=%d s=%d base=%d sets=%s menus=%s'%(o['name'],n,o['s'],o['base'],o['sets'],o['menus']))
    print('  L* = %.5f   L01 (best 0/1 price set) = %s  |U|=%s'%(o['L'],('%.5f'%o['L01']) if 'L01' in o else '-',len(o.get('U01') or [])))
    for lab in ('pi_sparse','pi_flat'):
        pi=o[lab]; mn=min(pi.values())
        print('  %s: support %d, values/min: %s ; mu=%s'%(lab,len(pi),sorted({round(p/mn,3) for p in pi.values()}),[round(x/mn,3) for x in o['mu_'+lab[3:]]]))
        for g in sorted(pi):
            r=R[g]; print('     g%-3d pi=%5.2f %-3s%-10s %-22s z0=%d units=%s cones=%s cntby=%s'%(g,pi[g]/mn,r['op'],r['ins'],','.join(r['tags']),r['z0'],r['units'],r['cones'],o['cntby'][g]))
    if o.get('U01'): print('  U01:',o['U01'])
if __name__=='__main__':
    res=[]
    for f in sys.argv[1:]:
        c=json.load(open(f)); nm=os.path.basename(f)[:-5]
        o=analyse(c,nm); res.append(o)
        pickle.dump(o,open(os.path.join(H,'out','dual_'+nm+'.pkl'),'wb'))
