# Coordinator's "relative sandwich" rule (my reading): set w may use z=0 or z = a minimal 1-point m of h, |m|<=2, m∩S_w=∅;
# system Σ(z) (atoms z+e_u, K=all); it charges only C_{w,z} = I_z(w) ∪ (P_w ∩ cnt_z(w)),
#   I_z(w) = {g∈cnt_z(w): g <= OR(S_w) on {x>=z}},  P_w = L_w ∪ U_w (fable A's sandwich classes A4).   L_rel = LP value (fraclp with this menu).
import sys, itertools
from lib import *
def tables(c):
    n,G=c['n'],c['gates']; X=list(itertools.product([0,1],repeat=n)); W=[ev(n,G,x) for x in X]; return X,W
def relmenus(c):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; ng=len(G); X,W=tables(c); idx={x:i for i,x in enumerate(X)}
    hw=[g for g in G if g[0]=='not'][0][1]
    ones=[x for x,w in zip(X,W) if w[hw]==1]
    mins=[x for x in ones if sum(x)<=2 and not any(y!=x and all(a<=b for a,b in zip(y,x)) for y in ones)]
    val=lambda g,x: W[idx[tuple(x)]][g]
    M=[]; info=[]
    for w,R in enumerate(S):
        orS=lambda x: int(any(x[u] for u in R))
        zS=tuple(0 if v in R else 1 for v in range(n)); unit=lambda u: tuple(int(v==u) for v in range(n))
        L={g for g in range(n,n+ng) if all(W[i][g]<=orS(x) for i,x in enumerate(X)) and sum(val(g,unit(u)) for u in R)>=2}
        U={g for g in range(n,n+ng) if all(W[i][g]>=orS(x) for i,x in enumerate(X)) and val(g,zS)==0}
        P=L|U; menu={}
        for z in [tuple([0]*n)]+[m for m in mins if not any(m[u] for u in R)]:
            def at(u): p=list(z); p[u]=1; return tuple(p)
            cnt={g for g in range(n,n+ng) if val(g,z)==0 and sum(val(g,at(u)) for u in R)>=2}
            cube=[i for i,x in enumerate(X) if all(a>=b for a,b in zip(x,z))]
            I={g for g in cnt if all(W[i][g]<=orS(X[i]) for i in cube)}
            menu[frozenset(I|(P&cnt))]=(z,None)
        M.append(menu); info.append((sorted(P),{tuple(v for v in range(n) if z[v]):sorted(Cz) for Cz,(z,_) in menu.items()}))
    return M,info
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        worst=0
        for c in cs:
            for g in c['gates']:
                if g[0]=='not': del g[2:]
            M,info=relmenus(c); dem=[len(s)-1 for s in c['sets']]
            if any(all(len(C)<d for C in m) for m,d in zip(M,dem)): L=float('inf')
            else:
                M2=[{C:v for C,v in m.items() if len(C)>=d} for m,d in zip(M,dem)]; L=fraclp(c,M=M2)[0]
            worst=max(worst,L)
            if len(cs)==1: print(f.split('/')[-1],'L_rel =',L); [print('   set',s,'P',i[0],'menus z->C',i[1]) for s,i in zip(c['sets'],info)]
        if len(cs)>1: print(f.split('/')[-1],len(cs),'worst L_rel',worst)
