import random, collections, sys, time
exec(open('research/tools/l951_charging/inj951.py').read().split("def make_instance")[0])
def check_outputs(n,sets,gates,outs):
    for x in range(1<<n):
        w=wires(n,gates,x)
        for S,o in zip(sets,outs): assert w[o]==int(any(x>>v&1 for v in S)), "SCAFFOLD 0: outputs wrong"
def make_wide(rng):
    n=rng.randint(7,10); hubs=list(range(rng.randint(1,3))); els=[v for v in range(n) if v not in hubs]; rng.shuffle(els)
    sets=[]; ts=[]
    used_pairs=set()
    for c in hubs:
        for _ in range(rng.randint(2,3)):
            if not els: break
            t=els.pop(); S={c,t}
            if els and rng.random()<0.4: S.add(els.pop())
            # (1,1)-disjointness check
            if all(len(S & set(T))<=1 for T in sets): sets.append(sorted(S)); ts.append(t)
    rest=[v for v in range(n) if all(v not in S for S in sets)]
    while len(rest)>=2 and rng.random()<0.6: sets.append(sorted([rest.pop(),rest.pop()]))
    if len(ts)<2: return None
    gates=[]
    def add(op,a,b): gates.append((op,a,b)); return n+len(gates)-1
    # h: OR of singleton minterms from ts, optionally pair minterms (AND)
    hs=rng.sample(ts,rng.randint(2,len(ts))); terms=list(hs)
    if rng.random()<0.5 and len(ts)>=2:
        a,b=rng.sample(ts,2); terms=[t for t in terms if t not in (a,b)]+[add('and',a,b)]
    hw=terms[0]
    for t in terms[1:]: hw=add('or',hw,t)
    p=len(gates); N=add('not',hw,hw)
    pool=list(ts)
    for _ in range(rng.randint(2,7)):
        i,j=rng.sample(pool,2); cw=add('or',i,j); pool.append(cw)
        for _r in range(rng.randint(1,4)): add('or',cw,rng.choice(hubs+ts))
        if rng.random()<0.3: add('and',N,cw)
    for _ in range(rng.randint(0,3)):
        m=n+len(gates); add(rng.choice(['and','or']),rng.randrange(m),rng.randrange(m))
    outs=[]
    for S in sets:
        w=S[0]
        for v in S[1:]: w=add('or',w,v)
        outs.append(w)
    return n,sets,gates,p,outs
def mutate(rng,inst):
    n,sets,gates,p,outs=inst; gates=list(gates)
    # insert a random OR/AND gate just before the output chains (outputs keep working: chains read inputs only)
    first_out=min(outs)-(max(len(S) for S in sets))  # conservative
    k=rng.randrange(p+1,len(gates)+1)
    # only insert before the first chain gate to keep chain indices valid: rebuild chains after
    chain_start=len(gates)-sum(len(S)-1 for S in sets)
    k=rng.randint(p+1,chain_start)
    m=n+k
    new=(rng.choice(['or','or','and']),rng.randrange(m),rng.randrange(m))
    body=gates[:k]+[new]+gates[k:chain_start]
    shift=lambda w: w+1 if w>=n+k else w
    body=[(op,shift(a) if i>=k+1 else a,shift(b) if i>=k+1 else b) for i,(op,a,b) in enumerate(body)]
    gates2=list(body); outs2=[]
    for S in sets:
        w=S[0]
        for v in S[1:]: gates2.append(('or',w,v)); w=n+len(gates2)-1
        outs2.append(w)
    return n,sets,gates2,p,outs2
rng=random.Random(7); t0=time.time(); tot=collections.Counter(); first=None
while time.time()-t0<200:
    inst=make_wide(rng)
    if inst is None: continue
    n,sets,gates,p,outs=inst
    check_outputs(*inst[:3],outs)
    ex,z,cf=analyse(n,sets,gates,p); best=(ex-z,inst,ex,z,cf)
    for step in range(15):           # hill-climb toward excess - zero
        cand=mutate(rng,best[1])
        if len(cand[2])>60: break
        check_outputs(cand[0],cand[1],cand[2],cand[4])
        ex2,z2,cf2=analyse(cand[0],cand[1],cand[2],cand[3])
        tot['evaluated']+=1; tot['max excess']=max(tot['max excess'],ex2)
        if cf2: tot['conflict: '+cf2[0]]+=1; first=first or (cand,cf2)
        if ex2-z2>=best[0]: best=(ex2-z2,cand,ex2,z2,cf2)
    tot['instances']+=1; tot['max(excess-zero)']=max(tot.get('max(excess-zero)',-99),best[0])
    tot['excess>zero']+=best[2]>best[3]; tot['excess>=3']+=best[2]>=3
print(dict(tot)); print('first conflict:',first[1] if first else None)
if first: print(first[0])
