# FJ test: lifted joint sandwich. vars x_0..x_{n-1}, y (index n). intervals [o_w∧(y∨h), o_w∨(y∧h)]. Is there a monotone circuit with base-1 gates?
import sys, json, itertools, time, random
import sand
n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); mode=sys.argv[3]; cap=int(sys.argv[4]); dec=int(sys.argv[5]) if len(sys.argv)>5 else 1
base=sum(len(S)-1 for S in sets)
ESS=len(sys.argv)>6
X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
XY=[x+(y,) for x in X for y in (0,1)]
def test(h,s):
    b=[]
    for S in sets:
        lo={};hi={}
        for x in X:
            o=int(any(x[u] for u in S))
            for y in (0,1):
                lo[x+(y,)]=o&(y|h[x]); hi[x+(y,)]=o|(y&h[x])
        b.append((lo,hi))
    if ESS:
        return sand.solve(n+1,b,s,XY,ess=[{x+(y,):int(any(x[u] for u in S)) for x in X for y in (0,1)} for S in sets])
    return sand.solve(n+1,b,s,XY)
if mode=='all':
    _,F=sand.monotone_fns(n); H=[dict(zip(X,f)) for f in F if f[0]==0 and any(f)]
elif mode=='rand':
    _,F=sand.monotone_fns(n); random.seed(2); F=[f for f in F if f[0]==0 and any(f)]; H=[dict(zip(X,f)) for f in random.sample(F,min(len(F),100000))]
else:
    subs=[frozenset(c) for k in range(1,n+1) for c in itertools.combinations(range(n),k)]
    M=[(a,) for a in subs]+[(a,b) for a,b in itertools.combinations(subs,2) if not a<=b and not b<=a]
    H=[{x:int(any(all(x[i] for i in m) for m in ms)) for x in X} for ms in M]
t0=time.time(); k=0; bad=[]
for h in H:
    k+=1
    if test(h,base-dec):
        mins=[[i for i in range(n) if x[i]] for x in X if h[x] and not any(h[z] and z!=x and all(a<=b for a,b in zip(z,x)) for z in X)]
        bad.append(mins); print('FJ VIOLATION: lifted family computable with',base-dec,'gates; h minterms',mins,flush=True)
    if time.time()-t0>cap: break
print(sets,'base',base,'mode',mode,'tested',k,'of',len(H),'violations (size base-%d):'%dec,len(bad),'sec %.0f'%(time.time()-t0))
