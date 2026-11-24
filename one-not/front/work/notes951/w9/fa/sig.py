import sys; sys.path.insert(0,'.')
from lib import *
import itertools, pickle
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
files=[F+'chk/c.jsonl','/tmp/w5ess.jsonl',F+'w7/bad.jsonl',F+'w7/badT.jsonl',F+'w6B/tri_ess.jsonl',F+'w6B/pasch_ess.jsonl',F+'w6B/k4_ess.jsonl',F+'w6B/c5.jsonl',F+'w6B/rest.jsonl',F+'w8/cx1.json',F+'w8/cx2.json',F+'w8/cx3.json',F+'w8b/cxr.json',F+'w9/tw/cxtw3c.json']
def down(c):
    n,G=c['n'],c['gates']; N=nw(c); d={N}
    for k,g in enumerate(G):
        if any(j in d for j in g[1:]): d.add(n+k)
    return d
def sig(c):
    n,G=c['n'],c['gates']; h=hw(c)
    tt=tuple(ev(n,G,x)[h] for x in itertools.product([0,1],repeat=n))
    d=down(c)
    return (n,tuple(tuple(s) for s in c['sets']),tt,tuple(int(o in d) for o in c['outs']))
if __name__=='__main__':
    sigs={}
    for f in files:
        try: cs=load(f)
        except Exception as e: print('skip',f,e); continue
        k=0
        for c in cs:
            if not any(g[0]=='not' for g in c['gates']): continue
            s=sig(c)
            if s not in sigs: sigs[s]=c; k+=1
        print(f,len(cs),'new sigs',k)
    pickle.dump(sigs,open('sigs.pkl','wb')); print(len(sigs))
