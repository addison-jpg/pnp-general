# candidate universal weighting: p-biased random zero point z (real circuit, B3 menu Sigma(z), classes cnt_z(w)), sub-selection LP
from wl import *
def cnts(T,c):
    n=T.n; W=T.w['real']; gates=range(n,T.W); out=[]
    for wi,R in enumerate(c['sets']):
        rest=[v for v in range(n) if v not in R]; m={}
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz)
                cl=frozenset(g for g in gates if not (W[g]>>z)&1 and sum((W[g]>>(z|1<<u))&1 for u in R)>=2)
                assert len(cl)>=len(R)-1
                m[z]=(cl,r,len(rest))
        out.append(m)
    return out
def maxload(dem,ents):
    # ents: list of (w, class, lam) ; fixed lam (lam=None => free with sum_w lam=1). minimise max gate load with sub-selection
    var={}
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    v('L'); eq=[];ub=[]
    free=any(e[2] is None for e in ents)
    if free:
        for w in range(len(dem)): eq.append(({v(('lam',j)):1 for j,e in enumerate(ents) if e[0]==w},1))
    for j,(w,C,lam) in enumerate(ents):
        r={v(('x',j,g)):1 for g in C}
        if lam is None:
            r[v(('lam',j))]=-dem[w]; eq.append((r,0))
            for g in C: ub.append(({v(('x',j,g)):1,v(('lam',j)):-1},0))
        else:
            eq.append((r,dem[w]*lam))
            for g in C: ub.append(({v(('x',j,g)):1},lam))
    gates=sorted({g for _,C,_ in ents for g in C})
    for g in gates:
        r={v(('x',j,g)):1 for j,e in enumerate(ents) if g in e[1]}; r[v('L')]=-1; ub.append((r,0))
    def mat(rows):
        A=lil_matrix((len(rows),len(var))); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    Ae,be=mat(eq);Au,bu=mat(ub);cost=np.zeros(len(var));cost[0]=1
    res=linprog(cost,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=[(0,None)]*len(var),method='highs')
    return res.fun
PS=[0.5,0.75,0.9,1.0]
def run(name,c,free=True):
    T=TT(c)
    if not T.correct(): return None
    dem=[len(s)-1 for s in c['sets']]; M=cnts(T,c); out=[]
    for p in PS:
        ents=[]
        for w,m in enumerate(M):
            for z,(cl,r,k) in m.items():
                lam=(p**r)*((1-p)**(k-r)) if p<1 else (1.0 if r==k else 0.0)
                if lam>0: ents.append((w,cl,lam))
        out.append(maxload(dem,ents))
    if free: out.append(maxload(dem,[(w,cl,None) for w,m in enumerate(M) for z,(cl,r,k) in m.items()]))
    return out
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2]); mod=int(sys.argv[3]) if len(sys.argv)>3 else 1
    cs=[(n,c) for n,c in allcirc()+extra() if lo<=c['n']<=hi and any(g[0]=='not' for g in c['gates'])][::mod]
    st=collections.Counter(); worst=[0]*(len(PS)+1); wn=['']*(len(PS)+1); nb=collections.Counter()
    for name,c in cs:
        r=run(name,c)
        if r is None: continue
        st[tuple(x<=1+1e-7 for x in r)]+=1
        for i,x in enumerate(r):
            if x>worst[i]: worst[i]=x; wn[i]=name
        if min(r[:len(PS)])>1+1e-7: nb['allp>1']+=1; print('allp>1',name,c['n'],[round(x,3) for x in r],flush=True)
        if hi>7: print(name,c['n'],[round(x,3) for x in r],flush=True)
    print('p=',PS,'+free; <=1 pattern:',st); print('worst',[round(x,3) for x in worst],wn,nb)
