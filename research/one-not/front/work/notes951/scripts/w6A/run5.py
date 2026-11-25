import random, itertools, time, sys
from assign import monotone_funcs
from mincost import mincost, linear_systems
from collections import Counter
n=5; H=monotone_funcs(n); random.seed(int(sys.argv[1]))
systems=linear_systems(n,10,(2,)) if sys.argv[2]=='g' else linear_systems(n,6,(2,3,4))
dist=Counter(); t0=time.time(); ex=[]
while time.time()-t0<200:
    mt=random.choice(H); E=random.choice(systems)
    hf=lambda x,mt=mt: int(any(m&x==m for m in mt))
    hard=[S for S in E if hf(31&~sum(1<<u for u in S))]
    if len(hard)<2: continue
    b=mincost(n,E,hf,cap=4); dist[b[0]]+=1
    if b[0]>=2 and len(ex)<5: ex.append((b[0],[bin(m) for m in mt],E))
print(dict(dist)); [print(e) for e in ex]
