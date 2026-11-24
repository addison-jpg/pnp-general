# single (system,h) FJ test: h given as list of minterms
import sys, json, itertools, time, sand
n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); ms=json.loads(sys.argv[3]); dec=int(sys.argv[4])
base=sum(len(S)-1 for S in sets)
X=[tuple(x) for x in itertools.product([0,1],repeat=n)]; XY=[x+(y,) for x in X for y in (0,1)]
h={x:int(any(all(x[i] for i in m) for m in ms)) for x in X}
b=[]
for S in sets:
    lo={};hi={}
    for x in X:
        o=int(any(x[u] for u in S))
        for y in (0,1): lo[x+(y,)]=o&(y|h[x]); hi[x+(y,)]=o|(y&h[x])
    b.append((lo,hi))
t=time.time(); r=sand.solve(n+1,b,base-dec,XY)
print(sets,'h',ms,'base',base,'lifted family with',base-dec,'gates:',r,'sec %.0f'%(time.time()-t),flush=True)
