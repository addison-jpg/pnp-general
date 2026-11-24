# cxP2: refutes Hall for the repaired classes Pi** = Dr ∪ Pr ∪ D1 ∪ P0 ∪ D0 ∪ (per-minterm D0^M).
# Two m-sets S1={p,p',u..}, S2={q,q',v..}; h = x_p x_p' ∨ x_q x_q'; pool y_k=(S1[k]∧hq)∨(S2[k]∧hp) multiplexed;
# U0 side hidden by crossing junk K_i (>= pair outputs {p,q}, {p',q'}).
from plib import *
def build(m):
    n=2*m; b=B(n); S1=list(range(m)); S2=list(range(m,2*m)); p,pp,q,qq=0,1,m,m+1
    hp=b.g('and',p,pp); hq=b.g('and',q,qq); h=b.g('or',hp,hq); N=b.g('not',h)
    c1=b.g('or',p,q); c2=b.g('or',pp,qq)       # outputs of pair sets {p,q},{p',q'}
    y=[b.g('or',b.g('and',S1[k],hq),b.g('and',S2[k],hp)) for k in range(m)]
    G=b.OR(y)                                   # = hq∧o1 ∨ hp∧o2 ; m-1 shared merges
    outs=[]
    for (S,sel,j1,j2) in ((S1,hp,c1,c2),(S2,hq,c1,c2)):
        K=b.OR([j1]+S[1:]); K2=b.OR([j2,S[0]]+S[2:])
        W=b.g('and',b.g('and',N,K),K2)
        outs.append(b.g('or',b.g('or',G,sel),W))
    return b.out([S1,S2,[p,q],[pp,qq]],outs+[c1,c2])
if __name__=='__main__':
    for m in (5,8,9):
        c=build(m); T=C(c); print(m,T.status()); K=T.classes()
        U=[pi2(T,K,i) for i in range(T.m)]; U0=[pistar(K,i) for i in range(T.m)]
        for i in range(2):
            dm=d0m(T,i); print('  set',i,'d',T.d[i],'|Pi*|',len(U0[i]),'|Pi**|',len(U[i]),'per-minterm',{bin(M):len(s) for M,s in dm.items()})
        print('  |Pi**_1 ∪ Pi**_2|',len(U[0]|U[1]),'shared',len(U[0]&U[1]),'matching Pi**',match(T.d,U),'base',T.base)
        if m==8: json.dump(c,open('cxP2.json','w'))
