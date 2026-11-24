import sys,time
from lib import *
from collections import Counter
t0=time.time()
for f in sys.argv[1:]:
    cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
    H=Counter(); worst=(0,None)
    for i,c in enumerate(cs):
        if time.time()-t0>240: break
        for g in c['gates']:
            if g[0]=='not': del g[2:]
        L,lam,M=fraclp(c,False); H[round(L,3)]+=1
        if L>worst[0]: worst=(L,i,len(c['gates']),sum(len(s)-1 for s in c['sets']))
    print(f.split('/')[-1],sum(H.values()),'worst',worst,sorted(H.items()))
