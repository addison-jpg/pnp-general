import itertools, sys, random
from assign import monotone_funcs, options
def inc(oa,ob):
    Qb,hzb=ob[0],ob[1]
    return sum(1 for y,hy in oa[2] if not (y&Qb==0 and (not hzb or hy)))
def cost(oa,ob): return max(0,min(inc(oa,ob),inc(ob,oa))-1)
def mincost(n,sets,hf,cap=99):
    O=[options(n,S,hf) for S in sets]
    order=sorted(range(len(sets)),key=lambda i:len(O[i]))
    best=[cap+1,None]; assign={}
    def bt(k,c):
        if c>=best[0]: return
        if k==len(order): best[0]=c; best[1]=dict(assign); return
        i=order[k]
        for o in O[i]:
            cc=c+sum(cost(o,assign[j]) for j in assign)
            if cc<best[0]:
                assign[i]=o; bt(k+1,cc); del assign[i]
    bt(0,0); return best
def linear_systems(n,maxsets=6,sizes=(2,3)):
    cand=[S for k in sizes for S in itertools.combinations(range(n),k)]
    res=[]
    def rec(i,ch):
        if len(ch)>=2: res.append(tuple(ch))
        if len(ch)==maxsets: return
        for j in range(i,len(cand)):
            if all(len(set(cand[j])&set(c))<=1 for c in ch): rec(j+1,ch+[cand[j]])
    rec(0,[]); return res
if __name__=='__main__':
    n=int(sys.argv[1]); mode=sys.argv[2]; samp=int(sys.argv[3]) if len(sys.argv)>3 else 0
    H=monotone_funcs(n)
    systems=linear_systems(n,int(sys.argv[4]) if len(sys.argv)>4 else 6,(2,) if mode=='g' else (2,3))
    print('h',len(H),'systems',len(systems))
    from collections import Counter
    dist=Counter(); ex=[]
    pairs=[(mt,E) for mt in H for E in systems]
    random.seed(1)
    if samp: pairs=random.sample(pairs,min(samp,len(pairs)))
    for mt,E in pairs:
        hf=lambda x,mt=mt: int(any(m&x==m for m in mt))
        hard=[S for S in E if hf(((1<<n)-1)&~sum(1<<u for u in S))]
        if len(hard)<2: continue
        b=mincost(n,E,hf)
        dist[b[0]]+=1
        if b[0]>=2 and len(ex)<6: ex.append((b[0],[bin(m) for m in mt],E))
    print(dict(dist)); [print(e) for e in ex]
