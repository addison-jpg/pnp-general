# Does a collision-free assignment (P_w=z_Q, atoms y_u) exist? all sets treated as N-sets.
import itertools, sys, random
from functools import lru_cache
def monotone_funcs(n):
    # all monotone h with h(0)=0, as frozenset of minterms (antichains), nonempty
    pts=list(range(1,1<<n))
    res=[]
    def rec(i,chosen):
        if i==len(pts):
            if chosen: res.append(tuple(chosen))
            return
        p=pts[i]
        rec(i+1,chosen)
        if all(not (c & p)==c and not (p & c)==p for c in chosen): rec(i+1,chosen+[p])
    rec(0,[]); return res
def options(n,S,hf):
    full=(1<<n)-1; Sm=sum(1<<u for u in S); opts=[]
    rest=[v for v in range(n) if v not in S]
    for r in range(len(rest)+1):
        for ex in itertools.combinations(rest,r):
            Q=Sm|sum(1<<v for v in ex); zQ=full&~Q; hz=hf(zQ)
            cands=[]
            for u in S:
                out=full&~Q; c=[(1<<u,hf(1<<u))]
                if not hf(1<<u):
                    sub=[w for w in range(1<<n) if w&out==w and hf((1<<u)|w)]
                    mins=[w for w in sub if not any(x!=w and x&w==x for x in sub)]
                    c+=[((1<<u)|w,1) for w in mins]
                cands.append(c)
            for ch in itertools.product(*cands):
                if hz and sum(1 for y,hy in ch if not hy)>1: continue
                opts.append((Q,hz,ch))
    return opts
def side_ok(oa,ob):
    Qb,hzb=ob[0],ob[1]
    bad=sum(1 for y,hy in oa[2] if not (y&Qb==0 and (not hzb or hy)))
    return bad<=1
def pair_ok(oa,ob): return side_ok(oa,ob) or side_ok(ob,oa)
def solve(n,sets,hf):
    O=[options(n,S,hf) for S in sets]
    order=sorted(range(len(sets)),key=lambda i:len(O[i]))
    assign={}
    def bt(k):
        if k==len(order): return True
        i=order[k]
        for o in O[i]:
            if all(pair_ok(o,assign[j]) for j in assign):
                assign[i]=o
                if bt(k+1): return True
                del assign[i]
        return False
    return bt(0), assign
if __name__=='__main__':
    n=int(sys.argv[1])
    H=monotone_funcs(n); print('monotone h',len(H))
    edges=list(itertools.combinations(range(n),2))
    fails=0; tot=0
    for mt in H:
        hf=lambda x,mt=mt: int(any(m&x==m for m in mt))
        for r in range(2,len(edges)+1):
          for E in itertools.combinations(edges,r):
            hard=[S for S in E if hf(((1<<n)-1)&~sum(1<<u for u in S))]
            if len(hard)<2: continue
            tot+=1
            ok,_=solve(n,E,hf)
            if not ok:
                fails+=1
                if fails<=5: print('FAIL minterms',[bin(m) for m in mt],'edges',E)
    print('tot',tot,'fails',fails)
