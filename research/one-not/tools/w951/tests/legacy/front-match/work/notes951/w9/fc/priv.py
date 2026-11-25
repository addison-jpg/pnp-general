# Rule PRIV: set w picks a legal system whose counted set has >= d_w gates that NO other set counts in ANY legal system.
# If every set has one => MatchG with disjoint representatives. deficit_w = d_w - max_C |C \ U_{others}|.
import sys, time
from lib import *
from collections import Counter
def priv(c, M=None):
    if M is None: M=allsys.menus(c,False)
    U=[set().union(*m) if m else set() for m in M]; res=[]
    for w,m in enumerate(M):
        oth=set().union(*[U[v] for v in range(len(M)) if v!=w]) if len(M)>1 else set()
        best=max(m,key=lambda C:len(C-oth)); res.append((len(c['sets'][w])-1-len(best-oth), m[best]))
    return res
if __name__=='__main__':
    t0=time.time()
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        H=Counter(); step=max(1,len(cs)//200); ex=None
        for i,c in enumerate(cs):
            if time.time()-t0>240: break
            if i%step: continue
            for g in c['gates']:
                if g[0]=='not': del g[2:]
            r=priv(c); d=max(x[0] for x in r); H['PRIV ok' if d<=0 else 'PRIV FAILS']+=1
            if d>0 and ex is None: ex=(i,[x[0] for x in r])
        print(f.split('/')[-1],dict(H),ex)
