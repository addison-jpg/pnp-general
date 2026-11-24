# Rule R*: z_w = z_{S_w}, atoms z+e_u, K = all gates. cnt*(w) = {g: g(z_S)=0, g(z_S+e_u)=1 for >=2 u in S}
import json,sys,itertools
from collections import Counter
def ev(n,G,x):
    w=list(x)
    for g in G:
        if g[0]=='not': w.append(1-w[g[1]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return w
def cnt_z(c,wi,z):
    n,G=c['n'],c['gates']; S=c['sets'][wi]
    wz=ev(n,G,z); at=[]
    for u in S:
        p=list(z); p[u]=1; at.append(ev(n,G,p))
    return [i for i in range(n,n+len(G)) if wz[i]==0 and sum(a[i] for a in at)>=2]
def rstar(c):
    n=c['n']; return [cnt_z(c,wi,[0 if v in S else 1 for v in range(n)]) for wi,S in enumerate(c['sets'])]
def bmatch(Ds, demand):
    slots=[(i,k) for i in range(len(Ds)) for k in range(demand[i])]; owner={}
    def aug(slot, seen):
        for g in Ds[slot[0]]:
            if g in seen: continue
            seen.add(g)
            if g not in owner or aug(owner[g], seen): owner[g]=slot; return True
        return False
    return sum(1 for sl in slots if aug(sl,set()))
if __name__=='__main__':
    H=Counter()
    for f in sys.argv[1:]:
        ls=[open(f).read()] if f.endswith('.json') else open(f)
        for l in ls:
            c=json.loads(l); Ds=rstar(c); dem=[len(s)-1 for s in c['sets']]
            H['n']+=1; ok=bmatch(Ds,dem)==sum(dem); H['hall']+=ok
            H['disj']+= len(set().union(*map(set,Ds)))==sum(map(len,Ds))
            H['short']+= any(len(d)<k for d,k in zip(Ds,dem))
            if not ok and H['pr']<3: H['pr']+=1; print('FAIL',f,Ds,json.dumps(c))
    print(dict(H))
