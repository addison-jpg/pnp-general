# heavy split rule: v heavy (h(e_v)=1). B-sets (v not in S) fixed at z_{S_b} (pure C0 world, x_v=1);
# star sets (v in S) free over all zero points (LP) and also fixed at z=0. Report max loads.
import sys, json
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/A2s')
from run import load, tables, correct
import numpy as np
from scipy.optimize import linprog
def merges_at(c,T,w,z):
    n=c['n'];G=c['gates'];S=c['sets'][w]
    par={u:u for u in S}
    def find(u):
        while par[u]!=u: par[u]=par[par[u]];u=par[u]
        return u
    B={}
    for v in S: B[v]=frozenset([v])
    M=0
    for k,g in enumerate(G):
        i=n+k
        if T[i]>>z&1: continue
        B[i]=frozenset(u for u in S if T[i]>>(z|1<<u)&1)
        if g[0]=='or':
            a=B.get(g[1]);b=B.get(g[2])
            if a and b:
                rs={find(u) for u in a|b}
                if len(rs)>1:
                    rs=sorted(rs)
                    for x in rs[1:]: par[x]=rs[0]
                    M|=1<<k
    return M
def zeropoints(n,S):
    rest=[v for v in range(n) if v not in S]
    for r in range(1<<len(rest)):
        z=0
        for i,v in enumerate(rest):
            if r>>i&1: z|=1<<v
        yield z
def run(name,c,out):
    n=c['n']
    if n>12: return
    T=tables(c)
    if not correct(c,T): return
    G=c['gates']; nots=[k for k,g in enumerate(G) if g[0]=='not']
    if len(nots)!=1: return
    h=T[G[nots[0]][1]]
    sets=c['sets']; pts=sorted(set(u for S in sets for u in S))
    heavy=[v for v in pts if h>>(1<<v)&1]
    ng=len(G)
    for v in heavy:
        A=[w for w,S in enumerate(sets) if v in S]; Bs=[w for w,S in enumerate(sets) if v not in S]
        fixed=np.zeros(ng)
        for b in Bs:
            zb=sum(1<<u for u in range(n) if u not in sets[b])
            M=merges_at(c,T,b,zb)
            for k in range(ng):
                if M>>k&1: fixed[k]+=1
        # integral: A at z=0
        l0=fixed.copy()
        for w in A:
            M=merges_at(c,T,w,0)
            for k in range(ng):
                if M>>k&1: l0[k]+=1
        # LP: A free
        fams=[sorted(set(merges_at(c,T,w,z) for z in zeropoints(n,sets[w]))) for w in A]
        nv=sum(len(f) for f in fams)+1
        cobj=np.zeros(nv); cobj[-1]=1
        Aub=np.zeros((ng,nv)); bub=-fixed.copy()
        col=0
        for f in fams:
            for M in f:
                for k in range(ng):
                    if M>>k&1: Aub[k,col]=1
                col+=1
        Aub[:,-1]=-1
        Aeq=np.zeros((len(fams),nv)); col=0
        for i,f in enumerate(fams):
            Aeq[i,col:col+len(f)]=1; col+=len(f)
        r=linprog(cobj,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=np.ones(len(fams)),bounds=[(0,None)]*nv,method='highs')
        L=r.fun if r.status==0 else None
        out.append((name,v,len(A),len(Bs),fixed.max() if ng else 0,l0.max(),L))
if __name__=='__main__':
    out=[]
    for f in sys.argv[1:]:
        for name,c in load(f):
            try: run(name,c,out)
            except Exception as e: print('ERR',name,e)
    import collections
    print('heavy (circuit,v) pairs:',len(out))
    print('max fixed-B load:',max(o[4] for o in out))
    print('max integral (A at 0) load:',max(o[5] for o in out), ' #>1:',sum(1 for o in out if o[5]>1))
    Ls=[o[6] for o in out if o[6] is not None]
    print('max LP (B fixed, A free):',max(Ls),' #>1+1e-9:',sum(1 for x in Ls if x>1+1e-9))
    for o in sorted(out,key=lambda o:-(o[6] or 0))[:8]: print(o)
