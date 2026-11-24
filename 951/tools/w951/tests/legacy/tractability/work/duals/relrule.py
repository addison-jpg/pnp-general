# Relative-sandwich rule: menu item for set w and zero point z (z=0 on S_w, weight<=WT):
#   I_z(w) = { g gate : g(z)=0, g(z+e_u)=1 for >=2 u in S_w, g <= OR(S_w) on the upper cube {x>=z} }   (relative dedicated, D_w^z)
#          ∪ { g in P_w (function-level private-above) : g(z)=0 }
# all subsets of cnt_z(w) (system Σ(z), unit atoms, K=all).  LP over these items; L_rel<=1 <=> rule gives FracMatch.
import sys,json,os,itertools
import resid as RS, dualp
from dualp import Dual, roles, evalN
def relmenu(c,WT=2,above=False):
    n,G,S=c['n'],c['gates'],c['sets']; ng=len(G); R=1<<n
    X=[sum(1<<r for r in range(R) if r>>i&1) for i in range(n)]; full=(1<<R)-1
    w=list(X)
    for g in G: w.append(full^w[g[1]] if g[0]=='not' else (w[g[1]]&w[g[2]] if g[0]=='and' else w[g[1]]|w[g[2]]))
    OR=[0]*len(S)
    for i,s in enumerate(S):
        for v in s: OR[i]|=X[v]
    Dc,Pc=RS.private(c); M=[]
    for i,s in enumerate(S):
        rest=[v for v in range(n) if v not in s]; items={}
        for k in range(WT+1):
            for zs in itertools.combinations(rest,k):
                zr=sum(1<<v for v in zs); cube=full
                for v in zs: cube&=X[v]
                I=set()
                for g in range(n,n+ng):
                    if w[g]>>zr&1: continue
                    cntd=sum(w[g]>>(zr|1<<u)&1 for u in s)>=2
                    if not cntd: continue
                    if (w[g]&cube)&~OR[i]==0: I.add(g)
                    elif g in Pc[i]: I.add(g)
                    elif above and (OR[i]&cube)&~w[g]==0: I.add(g)
                items[frozenset(I)]=zs
        mx=[x for x in items if not any(x<y for y in items)]
        M.append([(sorted(x),items[x]) for x in mx])
    return M
def run(c,name='',WT=2,above=False,verbose=True):
    F=relmenu(c,WT,above); dem=[len(s)-1 for s in c['sets']]
    M=[[C for C,z in m] for m in F]
    if any(all(len(C)<d for C in m) for m,d in zip(M,dem)):
        if verbose: print('=== %s L_rel=INF: short sets'%name,[(w,[C for C in m]) for w,(m,d) in enumerate(zip(M,dem)) if all(len(C)<d for C in m)])
        return float('inf'),{},F
    L,pi,mu,D=RS.lpdual(M,dem)
    if verbose:
        R=roles(c); print('=== %s L_rel=%.4f (WT=%d above=%s) mu=%s'%(name,L,WT,above,[round(x/min(pi.values()),2) for x in mu]))
        print('    pi:',RS.fmt(pi,R))
        for w,m in enumerate(F):
            for C,z in m: print('    set',w,'z=',list(z),'item',C)
    return L,pi,F
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        for i,c in enumerate(cs):
            c=c.get('c',c); run(c,os.path.basename(f)+'#%d'%i)
