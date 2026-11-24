# two-world classes (s_fable). Uses jcut/bt.py TT.
import sys, itertools
sys.path.insert(0,'/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/w9/jcut')
from bt import TT, allcirc, load
import numpy as np
def classes(c, maxz=None):
    """returns T, list per set of dict: option-key -> frozenset(gates). keys: ('E',) easy full; ('0',z) world0; ('1',c) world1 (hard)"""
    T=TT(c); n=T.n; S=c['sets']; FULL=T.FULL
    w0,w1=T.w[0],T.w[1]; gates=range(n,T.W)
    ndep={T.Ni}
    for k,g in enumerate(T.G):
        if any(j in ndep for j in g[1:]): ndep.add(n+k)
    T.ndep=ndep
    res=[]; T.hard=[]
    for wi,R in enumerate(S):
        o=T.o[wi]; no=FULL^o; rest=[v for v in range(n) if v not in R]
        zS=sum(1<<v for v in rest); hard=(T.h>>zS)&1; T.hard.append(hard)
        opt={}
        if not hard:
            cl=frozenset(g for g in gates if (w1[g]&no)==0 and sum((w1[g]>>(1<<u))&1 for u in R)>=2)
            opt[('E',)]=cl
        else:
            for r in range(len(rest)+1):
                for zz in itertools.combinations(rest,r):
                    z=sum(1<<v for v in zz)
                    if (T.h>>z)&1:
                        cube=FULL
                        for v in zz: cube&=T.var[v]
                        bad=cube&no
                        cl=frozenset(g for g in gates if not (w0[g]>>z)&1 and (w0[g]&bad)==0 and sum((w0[g]>>(z|1<<u))&1 for u in R)>=2)
                        opt[('0',z)]=cl
                    else:
                        # ceiling c=z in U0: Dom={x in U0, x<= z|S}
                        dom=T.U0
                        for v in rest:
                            if v not in zz: dom&=FULL^T.var[v]
                        bad=dom&no
                        light=[u for u in R if not (T.h>>(1<<u))&1]
                        cl=frozenset(g for g in gates if (w1[g]&bad)==0 and sum((w1[g]>>(1<<u))&1 for u in light)>=2)
                        opt[('1',z)]=(cl,len(light))
        res.append(opt)
    return T,res
