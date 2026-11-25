import sys,random,itertools,time,pickle
sys.path.insert(0,'.')
from xplus import analyse
random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 1)
SYS={'sun3':(7,[(0,1,4),(0,2,5),(0,3,6)]),'tri':(6,[(0,1,2),(2,3,4),(4,5,0)]),'path3':(7,[(0,1,2),(2,3,4),(4,5,6)]),
     'pasch':(6,[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]),'fan':(7,[(0,1,2),(0,3,4),(0,5,6),(1,3,5)]),'cross':(5,[(0,2,3),(1,2,4)]),
     'two4':(7,[(0,1,2,3),(0,4,5,6)]),'dis33':(6,[(0,1,2),(3,4,5)])}
name=sys.argv[1]; n,sets=SYS[name]
def rand_h():
    k=random.randint(1,5); M=[]
    for _ in range(k):
        r=random.choice([1,1,2,2,3]); M.append(frozenset(random.sample(range(n),r)))
    M=[m for m in M if not any(o<m for o in M)]
    tt=tuple(int(any(all(x[v] for v in m) for m in M)) for x in itertools.product([0,1],repeat=n))
    return tt,sorted(set(tuple(sorted(m)) for m in M))
seen={}; t0=time.time(); out=[]
while time.time()-t0<float(sys.argv[3]) :
    tt,M=rand_h()
    if tt in seen: continue
    X,P,ch=analyse((n,tuple(sets),tt,tuple([1]*len(sets))))
    seen[tt]=(X,P)
    if not X and not P: out.append(M)
from collections import Counter
print(name,'classes',len(seen),Counter(seen.values()))
for M in out[:40]: print('  no X+:',M)
pickle.dump(out,open('nox_%s.pkl'%name,'wb'))
