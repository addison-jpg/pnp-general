import random, itertools, time, sys, signal
from assign import monotone_funcs, options
from mincost import cost, linear_systems
from collections import Counter
class TO(Exception): pass
def h_(s,f): raise TO()
signal.signal(signal.SIGALRM,h_)
def mc(n,sets,hf,cap):
    O=[options(n,S,hf) for S in sets]
    order=sorted(range(len(sets)),key=lambda i:len(O[i])); best=[cap+1]; assign={}
    def bt(k,c):
        if c>=best[0]: return
        if k==len(order): best[0]=c; return
        i=order[k]
        for o in O[i]:
            cc=c+sum(cost(o,assign[j]) for j in assign)
            if cc<best[0]: assign[i]=o; bt(k+1,cc); del assign[i]
    bt(0,0); return best[0]
n=5; H=monotone_funcs(n); random.seed(int(sys.argv[1]))
systems=linear_systems(n,int(sys.argv[3]),(2,) if sys.argv[2]=='g' else (2,3,4))
dist=Counter(); t0=time.time(); ex=[]
while time.time()-t0<int(sys.argv[4]):
    mt=random.choice(H); E=random.choice(systems)
    hf=lambda x,mt=mt: int(any(m&x==m for m in mt))
    if sum(1 for S in E if hf(31&~sum(1<<u for u in S)))<2: continue
    signal.alarm(3)
    try: b=mc(n,E,hf,3)
    except TO: dist['timeout']+=1; continue
    finally: signal.alarm(0)
    dist[b]+=1
    if b>=int(sys.argv[5]) and len(ex)<6: ex.append((b,[bin(m) for m in mt],E))
print(dict(dist),flush=True); [print(e) for e in ex]
