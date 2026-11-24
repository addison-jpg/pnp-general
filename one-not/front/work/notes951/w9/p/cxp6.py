# cxP6: the cxP5 gadget inside a CORE system (every point in >= 2 sets of size >= 3, a 4-set): |Pi*_a| = 2 < 3.
from plib import *
def build():
    n=9; sets=[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7],[0,6,8],[2,7,8],[3,5,8]]
    b=B(n); S=[0,1,2,3]
    hB=b.g('and',5,6); h=b.g('or',4,hB); N=b.g('not',h)       # minterms {4}, {5,6}; both avoid S_a
    outs=[None]+[b.OR(s) for s in sets[1:]]
    oc,od=outs[1],outs[2]                                      # o_c = x0∨x4∨x5, o_d = x1∨x4∨x6
    K=b.OR([oc,1,2,3]); K2=b.OR([od,0,2,3])                    # K∧K2 = o_a ∨ x4 ∨ x5x6 = o_a ∨ h
    RA=b.OR([b.g('and',u,4) for u in S]); RB=b.OR([b.g('and',u,hB) for u in S])
    P=b.g('or',b.g('or',b.g('and',N,K),RA),RB)
    outs[0]=b.g('and',P,K2)
    return b.out(sets,outs)
if __name__=='__main__':
    c=build(); T=C(c); print(T.status()); K=T.classes()
    for i in range(T.m): print('  ',T.sets[i],'d',T.d[i],'hard',T.hard[i],'|Pi*|',len(pistar(K,i)),'|Pi**|',len(pi2(T,K,i)),sorted(pistar(K,i)))
    print('matching Pi*',match(T.d,[pistar(K,i) for i in range(T.m)]),'Pi**',match(T.d,[pi2(T,K,i) for i in range(T.m)]),'base',T.base)
    from cxp34 import conflicts; print(conflicts(T))
    json.dump(c,open('cxP6.json','w'))
