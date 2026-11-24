# free-choice check: does some pair of B3 systems Sigma(z1),Sigma(z2) give a full matching for the two big sets (+ outputs of the rest)?
from plib import *
import itertools,sys
def free(c,big=(0,1)):
    T=C(c); men=[]
    for i in big:
        S=T.sets[i]; rest=[v for v in range(T.n) if v not in S]; m={}
        for k in range(1<<len(rest)):
            z=sum(1<<rest[j] for j in range(len(rest)) if k>>j&1)
            cz=T.cnt_z(i,z)
            if len(cz)>=T.d[i]: m[z]=cz
        men.append(m)
    others=[i for i in range(T.m) if i not in big]
    K=T.classes(); win=[]
    for z1,c1 in men[0].items():
        for z2,c2 in men[1].items():
            adj=[c1,c2]+[K['Dr'][i]|K['Pr'][i] for i in others]; dem=[T.d[i] for i in big]+[T.d[i] for i in others]
            if match(dem,adj)==sum(dem): win.append((z1,z2))
    return len(men[0]),len(men[1]),len(win),[(bin(a),bin(b),T.h>>a&1,T.h>>b&1) for a,b in win[:4]]
if __name__=='__main__':
    import cxp2,cxp1
    print('cxP2 m=5',free(cxp2.build(5)))
    print('cxP2 m=6',free(cxp2.build(6)))
