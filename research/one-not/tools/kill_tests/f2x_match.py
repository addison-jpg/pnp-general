# per-set / matching form of the step: leaving gates L(v)=F2(Q)\F2(Q+v); Fw = gates with a w-witness at Q.
import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2lib import *
CS=corpus(9)
for s in range(int(sys.argv[1]),int(sys.argv[2])): CS+=randgen(s,3000)
st=collections.Counter(); ex={}
def match(dem,adj):
    # dem: {w:d}, adj: {w:set(g)}; max bipartite b-matching via augmenting
    slots=[(w,i) for w in dem for i in range(dem[w])]; mg={}
    def aug(s,seen):
        for g in adj[s[0]]:
            if g in seen: continue
            seen.add(g)
            if g not in mg or aug(mg[g],seen): mg[g]=s; return True
        return False
    return sum(aug(s,set()) for s in slots)==len(slots)
for c in CS:
    S=c['S']
    for Q in range(1<<c['n']):
        al=aliveW(c,Q)
        if not al: continue
        cb=cube(c,Q); hh=c['h']&cb; mono=hh in (0,cb)
        F,r=stepinfo(c,Q); st['inst',mono]+=1
        Fw={w:{g for g in F if c['wm'].get((g,w),0)&cb} for w in al}
        anyM=False
        for v in r:
            L=F-F2(c,Q|1<<v); star=[w for w in al if v in S[w]]
            good=r[v][0]>=r[v][1]
            perset=all(len(Fw[w]&L)>=len(S[w])-1 for w in star)
            m=match({w:len(S[w])-1 for w in star},{w:Fw[w]&L for w in star})
            anyM|=m
            st['pt',mono,'good' if good else 'bad','perset' if perset else 'noperset','match' if m else 'nomatch']+=1
            k=('pt',mono,'good' if good else 'bad','perset' if perset else 'noperset','match' if m else 'nomatch'); ex.setdefault(k,(c['name'],Q,v))
        if not anyM: st['NO v with matching',mono]+=1; ex.setdefault(('NO v with matching',mono),(c['name'],Q))
for k in sorted(st,key=str): print(k,st[k],ex.get(k))
