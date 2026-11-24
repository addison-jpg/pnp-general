import sys, pickle, itertools, time
from functools import lru_cache
def analyse(sig, want='both'):
    n,sets,tt,isN=sig
    hval=lambda x: tt[int(''.join(map(str,x)),2)]
    def hset(ones): return hval([1 if v in ones else 0 for v in range(n)])
    allv=frozenset(range(n))
    heavy=[hset({u}) for u in range(n)]
    # minterms
    mint=[]
    for r in range(n+1):
        for M in itertools.combinations(range(n),r):
            M=frozenset(M)
            if hset(M) and not any(m<=M for m in mint): mint.append(M)
    m=len(sets); S=[frozenset(s) for s in sets]
    # ---- Thm X
    def bt(opts, ok):
        ch=[None]*m
        order=sorted(range(m),key=lambda w:len(opts[w]))
        def rec(k):
            if k==m: return True
            w=order[k]
            for o in opts[w]:
                if all(ok(w,o,order[j],ch[order[j]]) for j in range(k)):
                    ch[w]=o
                    if rec(k+1): return True
            return False
        return rec(0), ch
    optsX=[]
    for w in range(m):
        rest=sorted(allv-S[w]); L=[]
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=S[w]|frozenset(ex)
                if (not isN[w]) or hset(allv-Q)==0 or all(heavy):
                    if not any(q<=Q for q in L): L.append(Q)
        optsX.append(L)
    okX=lambda a,Qa,b,Qb: len(S[a]&Qb)<=1 or len(S[b]&Qa)<=1
    X,chX=bt(optsX,okX)
    if X or want=='X': return X,None,None
    # ---- X+
    optsP=[]
    for w in range(m):
        rest=sorted(allv-S[w]); L=set()
        for r in range(len(rest)+1):
            for ex in itertools.combinations(rest,r):
                Q=S[w]|frozenset(ex); ones=allv-Q; zU1=hset(ones)
                per=[]
                for u in sorted(S[w]):
                    a=[(frozenset({u}),heavy[u])]
                    for M in mint:
                        if (M-{u})<=ones and M!=frozenset({u}): a.append((M|{u},1))
                    per.append(a)
                for combo in itertools.product(*per):
                    nU0=sum(1 for p,hv in combo if not hv)
                    if (not zU1) or nU0<=1: L.add((Q,zU1,False,combo))
                    if not isN[w]: L.add((Q,zU1,True,combo))
        optsP.append(sorted(L,key=lambda o:(len(o[0]),o[2])))
    def blocked(oa,ob):
        Qa,za1,ma,at=oa; Qb,zb1,mb,_=ob; k=0
        for p,hv in at:
            if (p&Qb) or ((not hv) and zb1 and not (ma or mb)): k+=1
        return k
    @lru_cache(None)
    def okc(a,ia,b,ib):
        return blocked(optsP[a][ia],optsP[b][ib])<=1 or blocked(optsP[b][ib],optsP[a][ia])<=1
    idx=[list(range(len(o))) for o in optsP]
    P,ch=bt(idx,lambda a,ia,b,ib: okc(a,ia,b,ib))
    return X,P,([optsP[w][ch[w]] for w in range(m)] if P else None)
if __name__=='__main__':
    sigs=pickle.load(open('sigs.pkl','rb')); t0=time.time()
    from collections import Counter; H=Counter(); res={}
    for i,s in enumerate(sigs):
        X,P,ch=analyse(s); res[s]=(X,P,ch)
        H[(X,P)]+=1
        if time.time()-t0>240: print('timeout at',i); break
    print(H, time.time()-t0)
    pickle.dump(res,open('xplus.pkl','wb'))
