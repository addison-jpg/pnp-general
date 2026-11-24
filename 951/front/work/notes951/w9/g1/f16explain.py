# f16explain.py: for the base-16 frontier systems print every class vector that survives the DFS and the first g* the bottom lemma cannot exclude
import json, cover2, collections
from cover import norm
orig=cover2.bottom_rule; log=[]
def wrap(sets,d,pts,Sv,l,P,sigma,Bs,explain=None,cls=None):
    ex=[]; r=orig(sets,d,pts,Sv,l,P,sigma,Bs,ex,cls)
    if not r: log.append((sorted(Bs),''.join(cls[u] for u in sorted(Bs)),ex))
    return r
cover2.bottom_rule=wrap
J=json.load(open('uncovered_after_round7.json')); cnt=collections.Counter()
for r in J['systems']:
    if r['base']>16: break
    S=norm(r['sets']); d,pts,Sv,l,P=cover2.info(S); log.clear(); cover2.feasible(S,True)
    print(r['rank'],r['sets'])
    for B,c,ex in log:
        Bs=set(B); cnt[ex[0][0]]+=1
        print('   B',''.join(map(str,B)),c,ex,'| V1:',' '.join(f"{u}(l{l[u]}p{len(P[u])}:"+'/'.join(''.join(map(str,sorted((X&Bs)-{u}))) for X in Sv[u])+")" for u in pts if u not in Bs))
print(cnt)
