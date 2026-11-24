# robustness of MergeFrac under random topological re-orderings of the gate list
from mg import *
import mg, random
def reorder(c,rng):
    n=c['n']; G=c['gates']; m=len(G); done=set(range(n)); order=[]; left=set(range(m))
    while left:
        ready=[k for k in left if all(j in done for j in G[k][1:])]
        k=rng.choice(ready); order.append(k); left.discard(k); done.add(n+k)
    pos={n+k:n+i for i,k in enumerate(order)}; f=lambda w: w if w<n else pos[w]
    return dict(n=n,sets=c['sets'],gates=[[G[k][0]]+[f(j) for j in G[k][1:]] for k in order],outs=[f(o) for o in c['outs']])
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1])); reps=int(sys.argv[2]); names=sys.argv[3:]
    cs=[(n,c) for n,c in allcirc()+extra() if any(k in n for k in names) and any(g[0]=='not' for g in c['gates'])]
    from cxrb import cxrb
    if 'cxrb' in names: cs+=[('cxrb%d'%k,cxrb(k)) for k in (4,6)]
    worst=(0,''); bad=0; tot=0
    for name,c in cs:
        for r in range(reps):
            c2=reorder(c,rng); L,a=mg.run(name,c2); tot+=1
            if L>worst[0]: worst=(L,name)
            if L>1+1e-7 or a: bad+=1; print('BAD',name,L,a); json.dump(c2,open('mgbad_%d.json'%bad,'w'))
        print(name,c['n'],'ok so far; worst',worst,flush=True)
    print('tot',tot,'bad',bad)
