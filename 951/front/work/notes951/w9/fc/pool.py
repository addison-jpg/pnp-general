# For triples (d=2): output o_w is counted by every legal system of w and by no system of another set (PROVED, see log C2),
# so free-choice MatchG/FracMatch restricted to triples+pairs <=> SDR for M_w = union over ALL legal systems of cnt \ {o_w}.
# slack(c) = min over nonempty families F of triples of |U_{w in F} M_w| - |F|   (>=0 <=> MatchG and FracMatch hold).
import sys, itertools
from lib import *
def mergesets(c):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; ng=len(G)
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]
    down={nw}
    for k,g in enumerate(G):
        if any(j in down for j in g[1:]): down.add(n+k)
    res=[]
    for wi,R in enumerate(S):
        M=set(); rest=[v for v in range(n) if v not in R]
        for zm in itertools.product([0,1],repeat=len(rest)):
            z=[0]*n
            for v,b in zip(rest,zm): z[v]=b
            wz=ev(n,G,z); ones=[v for v in rest if z[v]]
            zero=[i for i in range(n,n+ng) if wz[i]==0]
            A={u:[set(),set()] for u in R}   # A[u][N-value at atom] = gates (zero at z) true at some atom of u
            for u in R:
                for r in range(len(ones)+1):
                    for T in itertools.combinations(ones,r):
                        p=[0]*n; p[u]=1
                        for v in T: p[v]=1
                        wp=ev(n,G,p); A[u][wp[nw]].update(i for i in zero if wp[i])
            for u,v in itertools.combinations(R,2):
                au=A[u][0]|A[u][1]; av=A[v][0]|A[v][1]
                if wz[nw]==1 or len(R)<=2: M|=au&av          # Good: N true at z
                else:
                    if len(R)==2: M|=au&av
                    else: M|=(A[u][0]&av)|(au&A[v][0])        # N true at <=1 atom (third atom can always be made heavy)
                    if outs[wi] not in down: M|=(au&av)-down   # NOT-free K
        M.discard(outs[wi]); res.append(M)
    return res
def slack(c, M=None):
    if M is None: M=mergesets(c)
    tr=[w for w,s in enumerate(c['sets']) if len(s)==3]; best=(99,None)
    for r in range(1,len(tr)+1):
        for F in itertools.combinations(tr,r):
            v=len(set().union(*[M[w] for w in F]))-len(F)
            if v<best[0]: best=(v,F)
    return best
if __name__=='__main__':
    from collections import Counter
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        H=Counter(); worst=(99,)
        for i,c in enumerate(cs):
            for g in c['gates']:
                if g[0]=='not': del g[2:]
            if max(len(s) for s in c['sets'])!=3: continue
            M=mergesets(c); sl=slack(c,M); H[sl[0]]+=1
            if sl[0]<worst[0]: worst=(sl[0],sl[1],i,len(c['gates']),c['sets'],[sorted(m) for m in M])
        print(f.split('/')[-1],sorted(H.items()),'worst',worst)
