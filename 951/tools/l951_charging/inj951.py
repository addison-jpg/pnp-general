# Targeted injectivity test for the L-meta-951 charging rule.
import random, itertools, collections, sys
def wires(n,gates,x):
    w=[(x>>i)&1 for i in range(n)]
    for op,a,b in gates:
        A=w[a] if a<len(w) else 0; B=w[b] if b<len(w) else 0
        w.append(1-A if op=='not' else (A&B if op=='and' else A|B))
    return w
def transversal(n,mins):
    for k in range(n+1):
        for c in itertools.combinations(range(n),k):
            cm=sum(1<<i for i in c)
            if all(m&cm for m in mins): return cm
def analyse(n,sets,gates,p):
    full=(1<<n)-1; allw={x:wires(n,gates,x) for x in range(1<<n)}
    # SCAFFOLD 1: circuit computes the sums (outputs = last gate of each set's chain, passed in)
    hw=gates[p][1]; h=lambda x: allw[x][hw] if hw<n+p else 0
    mins=[x for x in range(1<<n) if h(x) and all(not h(x&~(1<<i)) for i in range(n) if x>>i&1)]
    merges=collections.defaultdict(list); info=[]
    for si,S in enumerate(sets):
        sm=sum(1<<v for v in S)
        miss=[m for m in mins if not m&sm]
        TS=transversal(n,miss) if miss else 0
        TS&=~sm
        Z=full&~(sm|TS)
        assert not h(Z), "SCAFFOLD: h must be 0 at zero point"
        wZ=allw[Z]
        for w in range(n+len(gates)):            # SCAFFOLD 2: invariant
            if wZ[w]==0:
                for x in range(n):
                    if not ((sm|TS)>>x&1): assert allw[1<<x][w]==0, "SCAFFOLD: invariant broken"
        par={u:u for u in S}
        def f(x):
            while par[x]!=x: x=par[x]
            return x
        A=lambda w:[u for u in S if allw[1<<u][w]] if wZ[w]==0 else None
        cnt=0
        for k,(op,a,b) in enumerate(gates):
            if op!='or' or wZ[n+k]!=0: continue
            Aa,Ab=A(a),A(b)
            if Aa and Ab and f(Aa[0])!=f(Ab[0]):
                par[f(Aa[0])]=f(Ab[0]); merges[k].append((si,a,b)); cnt+=1
        assert cnt>=len(S)-1, "SCAFFOLD: per-set count"
    zero=[k for k in range(len(gates)) if k not in merges]
    doubles=[k for k,l in merges.items() if len(l)>=2]
    excess=sum(len(l)-1 for l in merges.values())
    # charging rule: crossing input = an input wire of the double gate that has nonempty sets for >=2 of its sets;
    # charge to the latest zero-merge gate among that wire's ancestors (incl. itself)
    def ancestors(w):
        seen=set(); st=[w]
        while st:
            v=st.pop()
            if v<n or v in seen: continue
            seen.add(v); op,a,b=gates[v-n]; st+= [a,b]
        return seen
    charge={}; conflict=None
    for k in doubles:
        op,a,b=gates[k]
        tgt=None
        for wi in (a,b):
            cands=[g for g in ancestors(wi) if (g-n) in zero]
            if cands: tgt=max(cands)-n if tgt is None else max(tgt,max(cands)-n)
        if tgt is None: conflict=('no zero-merge ancestor',k); break
        if tgt in charge.values(): conflict=('same gate charged twice',k,tgt); break
        charge[k]=tgt
    return excess,len(zero),conflict
def make_instance(rng):
    # sets through a common hub c, plus extra disjoint sets; (1,1)-disjoint by construction
    n=rng.randint(6,9); c=0; els=list(range(1,n)); rng.shuffle(els)
    k=min(rng.randint(2,4),(n-1)//2); sets=[]; ts=[]
    for i in range(k):
        t=els.pop(); r=els.pop() if els and rng.random()<0.6 else None
        sets.append(sorted([c,t]+([r] if r is not None else []))); ts.append(t)
    while len(els)>=2 and rng.random()<0.7: sets.append(sorted([els.pop(),els.pop()]))
    gates=[]; n_=n
    def add(op,a,b): gates.append((op,a,b)); return n_+len(gates)-1
    # h = OR of hub-set private elements (crossing minterms), maybe with an AND
    hs=rng.sample(ts,rng.randint(2,len(ts)))
    hw=hs[0]
    for t in hs[1:]: hw=add('or',hw,t)
    if rng.random()<0.3 and len(ts)>=2: hw=add('and',hw,rng.choice(ts))
    p=len(gates); N=add('not',hw,hw)
    # planted crossing wires reused across several pairs: x_ti OR x_tj, then OR with hub
    for _ in range(rng.randint(1,4)):
        i,j=rng.sample(range(len(ts)),2)
        cw=add('or',ts[i],ts[j]); add('or',cw,c)
        if rng.random()<0.5: add('or',cw,rng.choice(ts))
        if rng.random()<0.4: add('and',N,cw)
    # random junk
    for _ in range(rng.randint(0,4)):
        m=n+len(gates); add(rng.choice(['and','or']),rng.randrange(m),rng.randrange(m))
    # outputs: plain OR chains (guarantee correctness)
    outs=[]
    for S in sets:
        w=S[0]
        for v in S[1:]: w=add('or',w,v)
        outs.append(w)
    return n,sets,gates,p,outs
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
N=int(sys.argv[2]) if len(sys.argv)>2 else 3000
stats=collections.Counter(); worst=None; tested=0
for it in range(N):
    n,sets,gates,p,outs=make_instance(rng)
    for x in range(1<<n):                       # SCAFFOLD 0: outputs correct
        w=wires(n,gates,x)
        for S,o in zip(sets,outs): assert w[o]==int(any(x>>v&1 for v in S))
    excess,zero,conflict=analyse(n,sets,gates,p); tested+=1
    stats['excess>0']+=excess>0; stats['excess>zero']+=excess>zero
    if conflict: stats['charge-'+conflict[0]]+=1; worst=worst or (sets,gates,p,conflict)
print('instances',tested,dict(stats))
if worst: print('first conflict:',worst)
