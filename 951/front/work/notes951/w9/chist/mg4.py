from mg import *
def solve(c):
    T=TT(c); dem=[len(s)-1 for s in c['sets']]; Ms,_=merges(c,T)
    ents=[];info=[]
    for w,m in enumerate(Ms):
        by={}
        for z,cl in m.items(): by.setdefault(cl,[]).append(z)
        for cl,zs in by.items(): ents.append((w,cl)); info.append(zs)
    gates=sorted({g for _,C in ents for g in C}); gi={g:i for i,g in enumerate(gates)}
    # min L: sum_e lam_e [g in cl_e] <= L ; sum_{e of w} lam=1
    nv=len(ents)+1; A=lil_matrix((len(gates),nv)); Ae=lil_matrix((len(dem),nv))
    for j,(w,C) in enumerate(ents):
        Ae[w,j]=1
        for g in C: A[gi[g],j]=1
    for i in range(len(gates)): A[i,nv-1]=-1
    cost=np.zeros(nv); cost[-1]=1
    res=linprog(cost,A_ub=A.tocsr(),b_ub=np.zeros(len(gates)),A_eq=Ae.tocsr(),b_eq=np.ones(len(dem)),bounds=[(0,None)]*nv,method='highs')
    return T,ents,info,res
if __name__=='__main__':
    for f in sys.argv[1:]:
        c=load(f)[0]; T,ents,info,res=solve(c); n=T.n
        print(f,'L*',round(res.fun,4),'h minterms:',[bin(z) for z in range(1<<n) if (T.h>>z)&1 and not any((T.h>>(z&~(1<<v)))&1 for v in range(n) if z>>v&1)][:12])
        for j,(w,C) in enumerate(ents):
            if res.x[j]>1e-7:
                zs=info[j]; print('  set',w,c['sets'][w],'lam',round(res.x[j],3),'merges',sorted(C),'#z',len(zs),'h(z) values',sorted({(T.h>>z)&1 for z in zs}),'e.g. z=',[v for v in range(n) if zs[0]>>v&1],'| max z',[v for v in range(n) if max(zs,key=lambda z:bin(z).count('1'))>>v&1])
