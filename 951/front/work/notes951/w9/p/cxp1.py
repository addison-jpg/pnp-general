# cxP1: refutes (a) |Pi*_w| >= d_w. Minterm-split on the U1 side + crossing-join junk on the U0 side.
from plib import *
def build(m=5, extra=True):
    # S_a = {0..m-1}; junk points J1=m, J2=m+1 (S_c={J1,0}, S_d={J2,1}); second minterm points m+2,m+3
    n=m+4; b=B(n); J1,J2,Q1,Q2=m,m+1,m+2,m+3
    sets=[list(range(m)),[J1,0],[J2,1]]
    hA=b.g('and',J1,J2); hB=b.g('and',Q1,Q2); h=b.g('or',hA,hB); N=b.g('not',h)
    oc=b.g('or',J1,0); od=b.g('or',J2,1)
    K=b.OR([oc]+list(range(1,m)))                 # = OR(S_a) v x_J1, every gate >= o_c
    K2=b.OR([od,0]+list(range(2,m)))              # = OR(S_a) v x_J2, every gate >= o_d
    M=b.g('and',b.g('and',N,K),K2)                # = OR(S_a) on U0, 0 on U1
    RA=b.OR([b.g('and',u,hA) for u in range(m)])  # OR(S_a) & hA
    RB=b.OR([b.g('and',u,hB) for u in range(m)])
    oa=b.g('or',M,b.g('or',RA,RB))
    outs=[oa,oc,od]
    if extra:
        sets+= [[Q1,2],[Q2,3]]; outs+=[b.g('or',Q1,2),b.g('or',Q2,3)]
    return b.out(sets,outs)
if __name__=='__main__':
    for m in (4,5,6):
        c=build(m); T=C(c); print(m,T.status())
        K=T.classes()
        for i in range(T.m):
            print('  set',T.sets[i],'d',T.d[i],'hard',T.hard[i],{k:sorted(K[k][i]) for k in K if K[k][i]},'|Pi*|',len(pistar(K,i)))
        U=[pistar(K,i) for i in range(T.m)]
        print('  matching',match(T.d,U),'base',T.base)
        mt=T.minterms(); print('  minterms',[bin(x) for x in mt])
        for z in mt:
            if all(not z>>u&1 for u in T.sets[0]): print('   cnt_z(a) at minterm',bin(z),len(T.cnt_z(0,z)))
        if m==5: json.dump(c,open('cxP1.json','w'))
