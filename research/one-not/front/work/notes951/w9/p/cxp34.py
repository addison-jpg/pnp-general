from plib import *
def conflicts(T,K=None,names=('Dr','Pr','D0','P0','D1')):
    K=K or T.classes(); res=[]
    for i in range(T.m):
        for j in range(T.m):
            if i==j: continue
            for a in names:
                for b in names:
                    for g in K[a][i]&K[b][j]:
                        if (a,i)<(b,j): res.append((a,i,'hard' if T.hard[i] else 'easy',b,j,'hard' if T.hard[j] else 'easy',g))
    return res
def p3():
    # D1_a ∩ Pr_c: S_a={1,2,3,4} hard, S_c={0,1}, h=x0 (0 heavy). Shannon split on x0.
    n=5; b=B(n); N=b.g('not',0); oc=b.g('or',0,1)
    K=b.OR([oc,2,3,4]); M=b.g('and',N,K); R=b.OR([b.g('and',u,0) for u in (1,2,3,4)])
    return b.out([[1,2,3,4],[0,1]],[b.g('or',M,R),oc])
def p4():
    # multiplexed gate g = N∧(x1∨x2) ∨ x0∧(x3∨x4): in Dr_w (w={0,1,2} easy) and D0_j (j={3,4,5} hard); h=x0
    n=6; b=B(n); N=b.g('not',0)
    y1=b.g('or',b.g('and',N,1),b.g('and',0,3)); y2=b.g('or',b.g('and',N,2),b.g('and',0,4)); g=b.g('or',y1,y2)
    ow=b.g('or',0,b.g('and',N,g))
    oj=b.g('or',b.g('or',b.g('and',0,g),b.g('and',N,b.g('or',3,4))),5)
    return b.out([[0,1,2],[3,4,5]],[ow,oj]),g
if __name__=='__main__':
    c=p3(); T=C(c); print('cxP3',T.status()); print(conflicts(T)); json.dump(c,open('cxP3.json','w'))
    c,g=p4(); T=C(c); print('cxP4',T.status(),'g=',g); print(conflicts(T)); json.dump(c,open('cxP4.json','w'))
    K=T.classes(); print({k:[sorted(x) for x in K[k]] for k in K})
    import cxp1,cxp2
    for nm,c in (('cxP1',cxp1.build(5)),('cxP2(5)',cxp2.build(5))):
        T=C(c); print(nm,conflicts(T))
