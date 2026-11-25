# all h with <=2 minterms (antichain), exhaustive
import sys, json, itertools, time
import sand
n=int(sys.argv[1]); sets=json.loads(sys.argv[2]); base=sum(len(S)-1 for S in sets)
X=[tuple(x) for x in itertools.product([0,1],repeat=n)]
subs=[frozenset(c) for k in range(1,n+1) for c in itertools.combinations(range(n),k)]
H=[(a,) for a in subs]+[(a,b) for a,b in itertools.combinations(subs,2) if not a<=b and not b<=a]
hist={}; t0=time.time(); bad=[]
for ms in H:
    h={x:int(any(all(x[i] for i in m) for m in ms)) for x in X}
    s0,s1=sand.sand(n,sets,h,X,base); hist[(s0,s1)]=hist.get((s0,s1),0)+1
    if max(s0,s1)<base: bad.append((s0,s1,[sorted(m) for m in ms])); print('max<base',bad[-1],flush=True)
    if time.time()-t0>260: print('time cap'); break
print(sets,'base',base,'tested',sum(hist.values()),'of',len(H),sorted(hist.items()))
