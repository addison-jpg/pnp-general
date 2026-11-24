import sys, json, itertools
from collections import Counter
def cone(n,G,o):
    seen,st=set(),[o]
    while st:
        i=st.pop()
        if i in seen or i<n: continue
        seen.add(i); st.extend(G[i-n][1:])
    return seen
def maxviol(c):
    """max over proper nonempty F of P(F)-d(F); minimal counterexample needs this <= -1"""
    n,G=c['n'],c['gates']; m=len(c['sets']); cn=[cone(n,G,o) for o in c['outs']]; d=[len(s)-1 for s in c['sets']]
    allg=set(range(n,n+len(G))); best=None
    for r in range(1,m):
        for F in itertools.combinations(range(m),r):
            rest=set().union(*[cn[w] for w in range(m) if w not in F])
            v=len(allg-rest)-sum(d[w] for w in F)
            if best is None or v>best[0]: best=(v,F)
    return best
if __name__=='__main__':
    for f in sys.argv[1:]:
        H=Counter(); cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        for c in cs:
            v,F=maxviol(c); H[v]+=1
        print(f,sorted(H.items()))
