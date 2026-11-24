# heavy split v2: B-sets (v not in S) float over zero points INSIDE the half-cube {x_v = 1} (pure C0, world 0);
# star sets (v in S) float over all their zero points. LP max load.
import sys, json
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/A2s')
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/heavy')
from run import load, tables, correct
from split import merges_at, zeropoints
import numpy as np
from scipy.optimize import linprog
def lp(fams, ng):
    nv=sum(len(f) for f in fams)+1
    cobj=np.zeros(nv); cobj[-1]=1
    Aub=np.zeros((ng,nv)); col=0
    for f in fams:
        for M in f:
            for k in range(ng):
                if M>>k&1: Aub[k,col]=1
            col+=1
    Aub[:,-1]=-1
    Aeq=np.zeros((len(fams),nv)); col=0
    for i,f in enumerate(fams):
        Aeq[i,col:col+len(f)]=1; col+=len(f)
    r=linprog(cobj,A_ub=Aub,b_ub=np.zeros(ng),A_eq=Aeq,b_eq=np.ones(len(fams)),bounds=[(0,None)]*nv,method='highs')
    return r.fun if r.status==0 else None
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
    full=[sorted(set(merges_at(c,T,w,z) for z in zeropoints(n,sets[w]))) for w in range(len(sets))]
    Lfull=lp(full,ng)
    for v in heavy:
        fams=[]
        for w,S in enumerate(sets):
            if v in S: fams.append(full[w])
            else: fams.append(sorted(set(merges_at(c,T,w,z) for z in zeropoints(n,S) if z>>v&1)))
        out.append((name,v,Lfull,lp(fams,ng),max(len(S) for S in sets)))
if __name__=='__main__':
    out=[]
    for f in sys.argv[1:]:
        for name,c in load(f):
            try: run(name,c,out)
            except Exception as e: print('ERR',name,e)
    print('pairs',len(out),' max full LP',max(o[2] for o in out),' max split-v2 LP',max(o[3] for o in out),
          ' #fail',sum(1 for o in out if o[3]>1+1e-9))
    for o in out:
        if o[3]>1+1e-9: print('FAIL',o)
