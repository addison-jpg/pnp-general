"""Seat A10: per-set single H0 zero point test.  python3 -I one-not/research/open/A10_maxY_test.py MAXN [GEN]
For each DD set w, every maximal Y in H0 = {h = 0} with Y >= 1_Q, Y = 0 on S_w u D; run the unit form at Y over S_w - D
with the heavy atoms pre-joined (>= need_w merges, asserted).  choice_fail = states where no choice of one Y per DD set
gives runs disjoint from each other and from the top family (A10 section 2)."""
import sys, collections, random, itertools
sys.path.insert(0, 'one-not/research/open')
import A7_dd_absorb_attack as A7, A10_light_attack as B
def run(G,W,n,zero,atoms,pre=()):
    lab={u:u for u in atoms}
    def find(u):
        while lab[u]!=u: u=lab[u]
        return u
    pre=list(pre)
    for u in pre[1:]: lab[find(u)]=find(pre[0])
    m=[]
    for k in range(len(G)):
        t=W[n+k]
        if t>>zero&1: continue
        r={find(u) for u in atoms if t>>atoms[u]&1}
        if len(r)>1:
            r=list(r)
            for x in r[1:]: lab[x]=r[0]
            m.append(k)
    return m
maxn=int(sys.argv[1]); rng=random.Random(1)
cs=A7.collect(maxn)
if len(sys.argv)>2: cs+=[A7.gen_switch(rng) for _ in range(int(sys.argv[2]))]
out=collections.Counter(); ex=[]
for c in cs:
    W,X,FULL=A7.tables(c['n'],c['gates'])
    if not A7.correct(c,W,X): continue
    n,G,S=c['n'],c['gates'],c['sets']
    p=[k for k,g in enumerate(G) if g[0]=='not'][0]; a=W[G[p][1]]
    for Q,D in A7.states(n,rng,-1 if n<=8 else 40):
        qpt=sum(1<<v for v in Q); ALL=(1<<n)-1
        alive=[]
        for w,R in enumerate(S):
            if set(R)&Q: continue
            R2=[u for u in R if u not in D]
            if len(R2)<2: continue
            zw=ALL
            for u in R2+list(D): zw&=~(1<<u)
            P={u:qpt|1<<u for u in R2}
            dd=bool(a>>zw&1) and any(not(a>>P[u]&1) for u in R2)
            alive.append((w,R2,zw,P,dd))
        if not any(x[4] for x in alive): continue
        out['dd_states']+=1
        top=set(); cand={}
        for (w,R2,zw,P,dd) in alive:
            if not dd: top|=set(run(G,W,n,zw,P)); continue
            U=[u for u in R2 if a>>P[u]&1]; T=[u for u in R2 if not a>>P[u]&1]
            if len(U)>=2: top|=set(run(G,W,n,zw,{u:P[u] for u in U}))
            need=len(T)-(0 if U else 1)
            # maximal Y in H0, >= qpt, 0 on S_w u D
            free=[v for v in range(n) if v not in Q and v not in D and v not in R2 and v not in S[w]]
            Ys=[]
            for mask in range(1<<len(free)):
                y=qpt
                for i,v in enumerate(free):
                    if mask>>i&1: y|=1<<v
                if a>>y&1: continue
                if any(not(a>>(y|1<<v)&1) for v in free if not y>>v&1): continue
                Ys.append(y)
            opts=[]
            for y in Ys:
                r=set(run(G,W,n,y,P,U))
                assert len(r)>=need, 'short'
                opts.append(frozenset(r))
            cand[w]=(opts,need)
        # any choice disjoint from top and pairwise?
        ws=list(cand)
        okc=[[o for o in cand[w][0] if not o&top] for w in ws]
        if any(not o for o in okc): out['no_Y_avoids_top']+=1
        found=False
        def rec(i,used):
            if i==len(ws): return True
            for o in okc[i]:
                if not o&used and rec(i+1,used|o): return True
            return False
        if all(okc) and rec(0,frozenset()): found=True
        out['choice_ok' if found else 'choice_fail']+=1
        if not found and len(ex)<4: ex.append((c['name'],sorted(Q),sorted(D),{w:[sorted(o) for o in cand[w][0]] for w in ws},sorted(top)))
print(dict(out))
for e in ex: print(e)
