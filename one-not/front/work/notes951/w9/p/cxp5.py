# cxP5: an m-set with |Pi*| = 2 (so a 4-set with |Pi*| = 2 < 3). AND-top version of cxP1 (configuration II' of T3).
from plib import *
def build(m=4):
    n=m+4; b=B(n); J1,J2,Q1,Q2=m,m+1,m+2,m+3
    hA=b.g('and',J1,J2); hB=b.g('and',Q1,Q2); h=b.g('or',hA,hB); N=b.g('not',h)
    oc=b.g('or',J1,0); od=b.g('or',J2,1)
    K=b.OR([oc]+list(range(1,m))); K2=b.OR([od,0]+list(range(2,m)))
    RA=b.OR([b.g('and',u,hA) for u in range(m)]); RB=b.OR([b.g('and',u,hB) for u in range(m)])
    P=b.g('or',b.g('or',b.g('and',N,K),RA),RB)
    oa=b.g('and',P,K2)
    return b.out([list(range(m)),[J1,0],[J2,1],[Q1,2],[Q2,3]],[oa,oc,od,b.g('or',Q1,2),b.g('or',Q2,3)])
if __name__=='__main__':
    for m in (4,5):
        c=build(m); T=C(c); print(m,T.status()); K=T.classes()
        i=0; print('  ',T.sets[i],'d',T.d[i],{k:sorted(K[k][i]) for k in K},'|Pi*|',len(pistar(K,i)),'|Pi**|',len(pi2(T,K,i)))
        U=[pistar(K,i) for i in range(T.m)]; print('  matching Pi*',match(T.d,U),'Pi**',match(T.d,[pi2(T,K,i) for i in range(T.m)]),'base',T.base)
        if m==4: json.dump(c,open('cxP5.json','w'))
