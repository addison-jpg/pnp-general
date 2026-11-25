import time, sys
from fast_synth import *
def path(n): return n, [(i,i+1) for i in range(n-1)]
def cyc(n): return n, [(i,(i+1)%n) for i in range(n)]
exp={'P3':2,'P4':4,'P5':5,'C4':3,'C5':7}
G={'P3':path(3),'P4':path(4),'P5':path(5),'C4':cyc(4),'C5':cyc(5)}
for sym in (False,True):
    for name,(n,E) in G.items():
        t=time.time()
        k,_=min_size(n,E,12,verbose=False,sym=sym)
        print(f"sym={sym} {name}: min={k} expected={exp[name]} {'OK' if k==exp[name] else 'MISMATCH'} ({time.time()-t:.1f}s)",flush=True)
