# Check the "top-2" theorem: for every set i, slots: o_i; if |S_i|>=3 one more gate:
#  OR-top  (o=A|B): input with >=2 units of S_i at z=0 (system Sigma(0)); AND-top (o=A&B): an input wire (leaf of star forest), z with leaf(z)=0.
# Verifies: chosen gates are gates, pairwise distinct, each in cnt_z(i) of the chosen Sigma(z).
import sys, json, itertools
from collections import Counter
def ev(n,G,x):
    w=list(x)
    for g in G:
        if g[0]=='not': w.append(1-w[g[1]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
def cntz(n,G,S,z):
    wz=ev(n,G,z); at=[]
    for u in S:
        p=list(z); p[u]=1; at.append(ev(n,G,p))
    return {i for i in range(n,n+len(G)) if wz[i]==0 and sum(a[i] for a in at)>=2}
def top2(c):
    n,G,sets,outs=c['n'],c['gates'],c['sets'],c['outs']
    big=[i for i,S in enumerate(sets) if len(S)>=3]
    andtop={}; chosen={}  # i -> (gate, z)
    for i in big:
        op,a,b=G[outs[i]-n][0],*G[outs[i]-n][1:]
        S=sets[i]
        if op=='or':
            z=[0]*n; cz=cntz(n,G,S,z); cand=[w for w in (a,b) if w in cz]
            if not cand: return 'FAIL or-top no dedicated',i
            chosen[i]=(cand[0],z)
        else: andtop[i]=(a,b)
    deg=Counter(w for e in andtop.values() for w in set(e))
    for i,(a,b) in andtop.items():
        if a==b or a<n or b<n: return 'FAIL and-top degenerate',i
        leaves=[w for w in (a,b) if deg[w]==1]
        if not leaves: return 'FAIL not star forest',i
        L=leaves[0]; S=sets[i]; rest=[v for v in range(n) if v not in S]; z=None
        for zm in itertools.product([0,1],repeat=len(rest)):
            zz=[0]*n
            for v,bb in zip(rest,zm): zz[v]=bb
            if ev(n,G,zz)[L]==0: z=zz; break
        if z is None: return 'FAIL leaf const',i
        if L not in cntz(n,G,S,z): return 'FAIL leaf not counted',i
        chosen[i]=(L,z)
    used=list(outs)+[g for g,_ in chosen.values()]
    if len(set(used))!=len(used): return 'FAIL not distinct',used
    return 'ok',Counter('or' if i not in andtop else 'and' for i in big)
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        H=Counter(); T=Counter()
        for c in cs:
            if not any(len(s)>=3 for s in c['sets']): H['nobig']+=1; continue
            r=top2(c); H[r[0]]+=1
            if r[0]=='ok': T.update(r[1])
            elif H[r[0]]<3: print(r, json.dumps(c)[:300])
        print(f,dict(H),dict(T))
