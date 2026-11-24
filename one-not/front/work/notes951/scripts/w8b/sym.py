# quotient search: states (b0,b1,b2,c), c in 0..r. functions as bitmasks.
import sys, itertools
r=int(sys.argv[1]); t=int(sys.argv[2]); n=r+3
ST=[(b,c) for b in range(8) for c in range(r+1)]; IDX={s:i for i,s in enumerate(ST)}
def mk(f): return sum(1<<i for i,(b,c) in enumerate(ST) if f(b,c))
pc=lambda b: bin(b).count('1')
X=[mk(lambda b,c,u=u: b>>u&1) for u in range(3)]
Nf=mk(lambda b,c: pc(b)+c<t)
OR=mk(lambda b,c: b!=0)
pool=set()
for i in range(0,t+1):
    for j in range(t,n+2):
        pool.add(mk(lambda b,c: i<=pc(b)+c<t or pc(b)+c>=j))
FULL=(1<<len(ST))-1
pool-={0,FULL}
# systems: z=(0,cz); atoms (1<<u, cu) cu<=cz
def countable(g):
    for cz in range(r+1):
        if g>>IDX[(0,cz)]&1: continue
        Nz = cz<t
        any_=[False]*3; n0=[False]*3
        for u in range(3):
            for cu in range(cz+1):
                if g>>IDX[(1<<u,cu)]&1:
                    any_[u]=True
                    if 1+cu>=t: n0[u]=True
        if Nz:
            if sum(any_)>=2: return True
        else:
            for u in range(3):
                for v in range(3):
                    if u!=v and n0[u] and any_[v]: return True
    return False
base=set(X)|pool
R=set(base); NCset=set()
frontier=set(base)
found=None
for it in range(6):
    new=set()
    L=list(R)
    for a in L:
        for b in L:
            if a>=b: continue
            if a not in frontier and b not in frontier: continue
            for g in (a&b,a|b):
                if g==OR: found=(a,b); 
                if g in R or g in new or g in (0,FULL): continue
                if not countable(g): new.add(g)
    print('iter',it,'R',len(R),'new',len(new),'found',found is not None,flush=True)
    if found or not new or len(R)+len(new)>6000: break
    R|=new; frontier=new
print('RESULT r',r,'t',t,'found',found)
