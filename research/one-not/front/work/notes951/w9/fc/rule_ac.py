# Rule AC: set w uses canonical unless a canonical-counted gate of w is also canonical-counted by another set; then w uses R*.
# Rule AC': mirror (R* unless R*-shared, then canonical).  Also EX2: exists per-set choice in {canonical, R*} with Hall.
import sys, time
from lib import *
from collections import Counter
def test(c):
    dem=[len(s)-1 for s in c['sets']]; base=sum(dem); Dc=canon(c); Dr=rstar(c); m=len(dem)
    sh=lambda D,w: any(set(D[w])&set(D[v]) for v in range(m) if v!=w)
    ac=[Dr[w] if sh(Dc,w) else Dc[w] for w in range(m)]
    acp=[Dc[w] if sh(Dr,w) else Dr[w] for w in range(m)]
    ex2=any(hbmatch([Dr[w] if (b>>w)&1 else Dc[w] for w in range(m)],dem)==base for b in range(1<<m)) if m<=12 else None
    return dict(AC=hbmatch(ac,dem)==base, ACm=hbmatch(acp,dem)==base, EX2=ex2, can=hbmatch(Dc,dem)==base, rs=hbmatch(Dr,dem)==base)
if __name__=='__main__':
    t0=time.time(); 
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        H=Counter(); step=max(1,len(cs)//2000)
        for i,c in enumerate(cs):
            if time.time()-t0>250: break
            if i%step: continue
            for g in c['gates']:
                if g[0]=='not': del g[2:]
            r=test(c); H['n']+=1
            for k,v in r.items(): H[k+' fails']+= (v is False)
        print(f.split('/')[-1],dict(H))
