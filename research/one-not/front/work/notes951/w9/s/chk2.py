from sl import *
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def lp(dem,opts):
    # opts: list per set of list of frozensets (each size>=dem). returns L*, duals
    var={}
    def v(k):
        if k not in var: var[k]=len(var)
        return var[k]
    v('L'); eq=[];ub=[]
    sysl=[(w,j,sorted(C)) for w,m in enumerate(opts) for j,C in enumerate(m)]
    for w,m in enumerate(opts): eq.append(({v(('lam',w,j)):1 for j in range(len(m))},1))
    for w,j,C in sysl:
        r={v(('y',w,j,g)):1 for g in C}; r[v(('lam',w,j))]=-dem[w]; eq.append((r,0))
        for g in C: ub.append(({v(('y',w,j,g)):1,v(('lam',w,j)):-1},0))
    gates=sorted({g for _,_,C in sysl for g in C}); grow={}
    for g in gates:
        r={v(('y',w,j,g)):1 for w,j,C in sysl if g in C}; r[v('L')]=-1; grow[g]=len(ub); ub.append((r,0))
    def mat(rows):
        A=lil_matrix((len(rows),len(var))); b=np.zeros(len(rows))
        for i,(r,bb) in enumerate(rows):
            for k,a in r.items(): A[i,k]=a
            b[i]=bb
        return A.tocsr(),b
    Ae,be=mat(eq);Au,bu=mat(ub);cost=np.zeros(len(var));cost[0]=1
    res=linprog(cost,A_ub=Au,b_ub=bu,A_eq=Ae,b_eq=be,bounds=[(0,None)]*len(var),method='highs')
    pi={g:-res.ineqlin.marginals[grow[g]] for g in gates}
    lam={(k[1],k[2]):res.x[i] for k,i in var.items() if k!='L' and k[0]=='lam' and res.x[i]>1e-9}
    return res.fun,pi,lam
if __name__=='__main__':
    import sys
    cs=allcirc(); worst=[]; viol=dict(EE=0,E0=0,E0indep=0,h00=0,h01=0,h01indep=0,h11=0,E1=0)
    for name,c in cs:
        if c['n']>12: continue
        T,res=classes(c); S=[set(s) for s in c['sets']]; dem=[len(s)-1 for s in S]
        opts=[]
        for wi,opt in enumerate(res):
            o=set()
            for k,cl in opt.items():
                if k[0]=='1':
                    if len(cl[0])>=dem[wi]: o.add(cl[0])
                else: o.add(cl)
            # keep minimal classes only
            o=[x for x in o if not any(y<x for y in o)]
            opts.append(o)
        # conflict lemma checks
        m=len(S)
        for a in range(m):
            for b in range(a+1,m):
                for ka,ca in res[a].items():
                    for kb,cb in res[b].items():
                        A=ca if ka[0]!='1' else ca[0]; B=cb if kb[0]!='1' else cb[0]
                        I=A&B
                        if not I: continue
                        ta,tb=ka[0],kb[0]
                        if ta=='E' and tb=='E': viol['EE']+=1
                        elif {ta,tb}=={'E','1'}: viol['E1']+=1
                        elif {ta,tb}=={'E','0'}:
                            viol['E0']+=1
                            if I-T.ndep: viol['E0indep']+=1
                        elif ta=='0' and tb=='0':
                            za,zb=ka[1],kb[1]
                            hit_ab=any(za>>v&1 for v in S[b]); hit_ba=any(zb>>v&1 for v in S[a])
                            if not(hit_ab and hit_ba): viol['h00']+=1
                        elif {ta,tb}=={'0','1'}:
                            viol['h01']+=1
                            if I-T.ndep: viol['h01indep']+=1
        L,pi,lam=lp(dem,opts)
        worst.append((L,name))
    worst.sort(reverse=True)
    print(viol); print(worst[:15])
    import collections
    print(collections.Counter(round(L,3) for L,_ in worst).most_common(12))
