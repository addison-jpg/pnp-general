# E4 test: all (1,1)-disjoint systems on <=N points (every point used, >=2 sets sharing structure not required), base<=B: essential-NOT circuit of size base+3?
import sys, itertools, json, time
sys.path.insert(0,'../g1')
import enumcores, ess
N=int(sys.argv[1]); B=int(sys.argv[2]); lo=int(sys.argv[3]); hi=int(sys.argv[4])
systems={}
def gen(n):
    alls=[frozenset(c) for k in range(2,n+1) for c in itertools.combinations(range(n),k)]
    level={():[]}
    while level:
        nxt={}
        for f,sets in level.items():
            if sets and len(set().union(*sets))==n: systems[(n,f)]=sets
            for S in alls:
                if all(len(S&T)<=1 for T in sets):
                    ns=sets+[S]
                    if sum(len(s)-1 for s in ns)>B: continue
                    ff=enumcores.canon(n,ns)
                    if ff not in nxt: nxt[ff]=ns
        level=nxt
for n in range(2,N+1): gen(n)
L=sorted(systems.items(),key=lambda kv:(sum(len(s)-1 for s in kv[1]),kv[0][0]))
print('systems',len(L),flush=True)
t0=time.time()
for idx,((n,f),sets) in enumerate(L[lo:hi]):
    base=sum(len(s)-1 for s in sets); S=[sorted(s) for s in sets]
    res,out,t=ess.solve(n,S,base+3,tmax=120,clean=False)
    print(lo+idx,n,S,'base',base,'essential at base+3:',res,'sec %.0f'%t,flush=True)
    if time.time()-t0>240: print('time cap at',lo+idx+1); break
