import json,sys,random,itertools
sys.path.insert(0,'../chk'); import chargeok_check as K, conedbl as C
from assign import options
from collections import Counter
random.seed(5); H=Counter()
for fn in ['../chk/c.jsonl','../chk/k.jsonl','/tmp/w5ess.jsonl']:
  for l in open(fn):
    c=C.norm(json.loads(l)); n,S,G,outs=c['n'],[tuple(x) for x in c['sets']],c['gates'],c['outs']
    nw=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=G[nw-n][1]
    ev=lambda m: K.evaluate(n,G,[(m>>i)&1 for i in range(n)])
    hf=lambda m: ev(m)[h]
    cones=[K.cone(n,G,o) for o in outs]
    if random.random()>0.05: continue
    for wi,R in enumerate(S):
        for (Q,hz,ch) in random.sample(options(n,R,hf),min(5,len(options(n,R,hf)))):
            P=ev(((1<<n)-1)&~Q); Y=[ev(y) for y,_ in ch]
            par={u:u for u in R}
            def f(u):
                while par[u]!=u: u=par[u]
                return u
            Bs=lambda i:{f(R[j]) for j in range(len(R)) if Y[j][i]}
            m=0; ok=True
            for i in sorted(cones[wi]):
                g=G[i-n]
                if P[i]!=0: continue
                if g[0]=='or':
                    ra,rb=Bs(g[1]),Bs(g[2])
                    if len(ra)>1 or len(rb)>1: ok=False
                    if ra and rb and ra!=rb: par[ra.pop()]=rb.pop(); m+=1
            H['ok' if ok and m>=len(R)-1 and P[outs[wi]]==0 else 'BAD']+=1
print(dict(H))
