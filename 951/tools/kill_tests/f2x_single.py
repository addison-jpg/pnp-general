# Does the plan's form hold: for some v, each alive w through v has a zero point Z_w (Z ⊇ Q, v ∉ Z) with M_Z(w) ⊆ L(v)=F2(Q)\F2(Q+v),
# and can the M_{Z_w}(w) be chosen pairwise disjoint?  (single-Z form of the step)
import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2lib import *
CS=corpus(7)
for s in range(int(sys.argv[1]),int(sys.argv[2])): CS+=[c for c in randgen(s,1500) if c['n']<=6]
st=collections.Counter(); ex={}
def sdr(opts):
    def rec(i,used):
        if i==len(opts): return True
        return any(not (o&used) and rec(i+1,used|o) for o in opts[i])
    return rec(0,frozenset())
for c in CS:
    S=c['S']; n=c['n']
    MZ={}
    for Q in range(1<<n):
        al=aliveW(c,Q)
        if not al: continue
        cb=cube(c,Q); hh=c['h']&cb; mono=hh in (0,cb)
        F,r=stepinfo(c,Q); st['inst',mono]+=1; res={}
        for v in r:
            L=F-F2(c,Q|1<<v); opts=[]
            for w in al:
                if v not in S[w]: continue
                o=set()
                for Z in range(1<<n):
                    if Z&Q!=Q or any(Z>>u&1 for u in S[w]): continue
                    if (w,Z) not in MZ: MZ[w,Z]=M(c,w,Z)
                    if MZ[w,Z]<=L: o.add(MZ[w,Z])
                opts.append(o)
            a=all(opts); b=a and sdr(opts)
            res[v]=(r[v][0]>=r[v][1],a,b)
            st['pt',mono,res[v]]+=1; ex.setdefault(('pt',mono,res[v]),(c['name'],Q,v))
        if not any(x[2] for x in res.values()): st['NO v with single-Z SDR',mono]+=1; ex.setdefault(('NO v with single-Z SDR',mono),(c['name'],Q))
        if not any(x[1] for x in res.values()): st['NO v with single-Z per set',mono]+=1; ex.setdefault(('NO v with single-Z per set',mono),(c['name'],Q))
for k in sorted(st,key=str): print(k,st[k],ex.get(k))
