import itertools, json, sys
sys.path.insert(0,'../../w8'); sys.path.insert(0,'../fa')
# PG(2,3): points = 1-dim subspaces of F_3^3
pts=[]
for v in itertools.product(range(3),repeat=3):
    if any(v) and next(x for x in v if x)==1: pts.append(v)
lines=[]
for l in pts:
    lines.append(sorted(i for i,p in enumerate(pts) if sum(a*b for a,b in zip(l,p))%3==0))
n=13; assert len(pts)==13 and all(len(l)==4 for l in lines)
a=lines[0]; b=[l for l in lines[1:] if set(l)&set(a)][0]
p=(set(a)&set(b)).pop(); q=[u for u in b if u!=p][0]
gates=[]
def G(*g): gates.append(list(g)); return n+len(gates)-1
outs={}
# line b: start with x_p | x_q
gb=G('or',p,q); w=gb
for u in b:
    if u not in (p,q): w=G('or',w,u)
outs[tuple(b)]=w
# clean gadget: line a2 through q (not p): x_q := (x_p & x_q) | (~x_p & (x_p|x_q))
a2=[l for l in lines if q in l and p not in l][0]
N=G('not',p); g4=G('and',p,q); g6=G('and',N,gb)
w=g6
for u in a2:
    if u!=q: w=G('or',w,u)
outs[tuple(a2)]=G('or',w,g4)
for l in lines:
    if tuple(l) in outs: continue
    w=l[0]
    for u in l[1:]: w=G('or',w,u)
    outs[tuple(l)]=w
c=dict(n=n,sets=lines,gates=gates,outs=[outs[tuple(l)] for l in lines])
json.dump(c,open('pg3_ess43.json','w'))
import verify, lib
print(verify.verify(c)); print('fa/lib verify (correct, C0 wrong, C1 wrong):',lib.verify(lib.norm(dict(c))))
