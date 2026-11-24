# frontier.py: run coverage with RULES (default 245pq, pure DFS) on a data set and collect the FRONTIER = uncovered systems
# that are not small3, have no R0 point, and all of whose point deletions are covered (the minimal uncovered systems met in the
# recursion, including sub-systems of the inputs).  Canonical form via enumcores.canon.  Output: pickle of {canon: record}.
# usage: python3 frontier.py RULES SOURCE [lo hi]     SOURCE in skel8, skel9, skel10, pair8, pair9
import sys, pickle
from cover import norm, degs, delete
import cover2
from enumcores import canon
rules=sys.argv[1]; src=sys.argv[2]
if src.startswith('skel'): L=[(s,0) for s in pickle.load(open(f'cores{src[4:]}.pkl','rb'))]
else: L=pickle.load(open(f'pairsys{src[4:]}.pkl','rb'))
lo,hi=(int(sys.argv[3]),int(sys.argv[4])) if len(sys.argv)>4 else (0,len(L))
L=L[lo:hi]
cv=sum(cover2.covered(s,rules) for s,k in L)
def relabel(S):
    pts=sorted(set().union(*S)); m={v:i for i,v in enumerate(pts)}
    return len(pts),[frozenset(m[v] for v in X) for X in S]
out={}
for (sets,r,gr),val in list(cover2.memo.items()):
    if r!=rules or val: continue
    if all(len(S)<=3 for S in sets): continue
    d=degs(sets)
    if any(sum(1 for S in sets if v in S and len(S)>=3)<=1 for v in d): continue
    if not all(cover2.memo.get((delete(sets,v),rules,gr), cover2.covered(delete(sets,v),rules)) for v in d): continue
    n,S2=relabel(sets); f=canon(n,S2)
    if f in out: continue
    sysl=sorted([sorted(X) for X in f],key=lambda x:(-len(x),x))
    out[f]=dict(n=n,base=sum(len(X)-1 for X in f),sets=sysl,npairs=sum(1 for X in f if len(X)==2),
                degrees=sorted(degs(norm(f)).values()),source=src)
pickle.dump(out,open(f'frontier_{rules}_{src}_{lo}_{hi}.pkl','wb'))
print(src,lo,hi,'rules',rules,'inputs',len(L),'covered',cv,'frontier systems (canonical)',len(out),
      'by base',sorted(__import__('collections').Counter(x['base'] for x in out.values()).items()))
