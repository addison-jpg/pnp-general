# random walk over correct clean live one-NOT circuits (honest start + junk relays + random rewires); checks uni.check on each
import sys, random, json, time, pickle
sys.path.insert(0,'..')
from g1lib import tts, _vm, varmask
from uni import check, summarize, is_correct, is_clean_live
def normalize(n,sets,gates,outs):
    """gates: list of [op,a,b] / ['not',a] with wire ids (n+index), any order. returns clean live circuit dict or None"""
    m=len(gates)
    # toposort
    order=[]; state={}
    def visit(i):
        st=[(i,0)]
        while st:
            w,ph=st.pop()
            if w<n: continue
            if ph==0:
                if state.get(w)==2: continue
                if state.get(w)==1: return False
                state[w]=1; st.append((w,1))
                for a in gates[w-n][1:]:
                    if a>=n and state.get(a)!=2:
                        if state.get(a)==1: return False
                        st.append((a,0))
            else:
                if state.get(w)!=2: state[w]=2; order.append(w)
        return True
    for o in outs:
        if not visit(o): return None
    for i in range(n,n+m):
        if state.get(i)!=2:
            if not visit(i): return None
    full=(1<<(1<<n))-1
    if n not in _vm: _vm[n]=[varmask(n,i) for i in range(n)]
    T={i:_vm[n][i] for i in range(n)}; canon={_vm[n][i]:i for i in range(n)}; alias={i:i for i in range(n)}
    for w in order:
        g=gates[w-n]; ins=[alias[a] for a in g[1:]]
        if any(a is None for a in ins): 
            # reads a constant: recompute by function
            pass
        vals=[T[a] if a is not None else None for a in ins]
        # constants stored in T under keys 'c0','c1'
        vals=[T[a] for a in ins]
        if g[0]=='not': t=full^vals[0]
        elif g[0]=='and': t=vals[0]&vals[1]
        else: t=vals[0]|vals[1]
        if t==0: alias[w]='c0'; T['c0']=0; continue
        if t==full: alias[w]='c1'; T['c1']=full; continue
        if t in canon: alias[w]=canon[t]
        else: canon[t]=w; alias[w]=w; T[w]=t
    # correctness
    newouts=[]
    for S,o in zip(sets,outs):
        t=0
        for u in S: t|=_vm[n][u]
        a=alias[o]
        if not isinstance(a,int) or a<n or T[a]!=t: return None
        newouts.append(a)
    need=set(); st=list(newouts)
    while st:
        i=st.pop()
        if i<n or i in need: continue
        need.add(i); st+=[alias[a] for a in gates[i-n][1:]]
    keep=[w for w in order if w in need]
    ren={w:n+k for k,w in enumerate(keep)}
    for i in range(n): ren[i]=i
    G=[]
    for w in keep:
        g=gates[w-n]; G.append([g[0]]+[ren[alias[a]] for a in g[1:]])
    if sum(g[0]=='not' for g in G)>1: return None
    return dict(n=n,sets=[list(S) for S in sets],gates=G,outs=[ren[o] for o in newouts])
def honest(n,sets,rng):
    gates=[]; outs=[]
    for S in sets:
        ws=list(S); rng.shuffle(ws)
        while len(ws)>1:
            i=rng.randrange(len(ws)); a=ws.pop(i); j=rng.randrange(len(ws)); b=ws.pop(j)
            gates.append(['or',a,b]); ws.append(n+len(gates)-1)
        outs.append(ws[0])
    return normalize(n,sets,gates,outs)
def formula(n,gates,rng,pool,depth=2):
    """append a random monotone formula over pool; return wire"""
    def term():
        k=rng.choice([1,1,2,2,3]); ws=rng.sample(pool,min(k,len(pool)))
        w=ws[0]
        for x in ws[1:]:
            gates.append(['or',w,x]); w=n+len(gates)-1
        return w
    k=rng.choice([1,2,2,3]); ts=[term() for _ in range(k)]
    w=ts[0]
    for x in ts[1:]:
        if x==w: continue
        gates.append(['and',w,x]); w=n+len(gates)-1
    return w
def mutate(c,rng):
    n=c['n']; sets=c['sets']; gates=[list(g) for g in c['gates']]; outs=list(c['outs']); m=len(gates)
    hasnot=any(g[0]=='not' for g in gates)
    mv=rng.random()
    allw=list(range(n+m))
    def rd(v): return [(k,j) for k,g in enumerate(gates) for j in range(1,len(g)) if g[j]==v]
    if mv<0.35:      # relay on a variable: r = x_v op c ; rewire (subset of) readers
        v=rng.randrange(n); pins=rd(v)
        if not pins: return None
        typ=rng.random()
        if typ<0.5:   # targeted OR junk: c = AND_S OR(sub of S\v) [& extra]
            ts=[]
            for S in sets:
                if v in S and len(S)>=2:
                    o=[u for u in S if u!=v]; k=rng.randint(1,len(o)); ts.append(rng.sample(o,k))
            if rng.random()<0.3: ts.append(rng.sample(range(n),rng.randint(1,2)))
            ws=[]
            for t in ts:
                w=t[0]
                for x in t[1:]: gates.append(['or',w,x]); w=n+len(gates)-1
                ws.append(w)
            w=ws[0]
            for x in ws[1:]:
                if x!=w: gates.append(['and',w,x]); w=n+len(gates)-1
            cw=w; op='or'
            if rng.random()<0.25 and not hasnot:
                gates.append(['not',cw]); cw=n+len(gates)-1; op='and'
                if rng.random()<0.5:
                    y=formula(n,gates,rng,list(range(n))); gates.append(['or',cw,y]); cw=n+len(gates)-1
        else:
            pool=[w for w in allw if w!=v]
            cw=rng.choice(pool) if rng.random()<0.5 else formula(n,gates,rng,pool)
            op=rng.choice(['or','and'])
        if cw==v: return None
        gates.append([op,v,cw]); r=n+len(gates)-1
        sub=pins if rng.random()<0.6 else rng.sample(pins,rng.randint(1,len(pins)))
        for k,j in sub: gates[k][j]=r
    elif mv<0.6:     # new gate + rewire one pin to it
        a,b=rng.sample(allw,2); op=rng.choice(['or','and'])
        gates.append([op,a,b]); w=n+len(gates)-1
        if rng.random()<0.3:
            c2=rng.choice(allw); gates.append([rng.choice(['or','and']),w,c2]); w=n+len(gates)-1
        k=rng.randrange(m); j=rng.randrange(1,len(gates[k])); gates[k][j]=w
    elif mv<0.8:     # rewire a pin to an existing wire
        k=rng.randrange(m); j=rng.randrange(1,len(gates[k])); gates[k][j]=rng.choice(allw)
    elif mv<0.9:     # NOT junk
        if hasnot:
            N=[n+k for k,g in enumerate(gates) if g[0]=='not'][0]
        else:
            gates.append(['not',rng.choice(allw)]); N=n+len(gates)-1
        a=rng.choice(allw); gates.append([rng.choice(['or','and']),N,a]); w=n+len(gates)-1
        if rng.random()<0.5:
            b=rng.choice(allw); gates.append([rng.choice(['or','and']),w,b]); w=n+len(gates)-1
        k=rng.randrange(m); j=rng.randrange(1,len(gates[k])); gates[k][j]=w
    else:            # change a gate type
        k=rng.randrange(m)
        if gates[k][0]=='not': return None
        gates[k][0]='and' if gates[k][0]=='or' else 'or'
    return normalize(n,sets,gates,outs)
SYS={
 'pasch':(6,[[0,1,2],[0,3,4],[1,3,5],[2,4,5]]),
 'paschP':(6,[[0,1,2],[0,3,4],[1,3,5],[2,4,5],[0,5],[1,4],[2,3]]),
 'paschP1':(6,[[0,1,2],[0,3,4],[1,3,5],[2,4,5],[0,5]]),
 'c7':(7,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4]]),
 'c7b':(7,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4],[3,5],[3,6]]),
 'fano':(7,[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]]),
 'core8':(8,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7]]),
 'f28':(8,[[4,5,6,7],[0,1,4],[0,2,5],[1,3,6],[2,3,7],[0,6],[1,7],[2,4],[3,5]]),
 'R0':(8,[[2,3,6,7],[0,1,6],[0,3,5],[1,2,4],[1,5,7],[4,5,6],[0,2],[1,3]]),
 'R3':(8,[[1,4,5,6],[2,3,5,7],[0,1,2],[0,3,6],[0,4,7],[0,5],[1,3],[2,4]]),
 'f0':(8,[[0,5,6,7],[0,3,4],[1,2,6],[1,4,5],[2,3,5],[2,4,7],[0,1],[0,2]]),
 'tri':(6,[[0,1,2],[2,3,4],[4,5,0],[1,3],[3,5],[5,1]]),
 'g33':(9,[[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8]]),
 'p5':(5,[[0,1,2],[0,3,4],[1,3],[2,4],[1,4],[2,3]]),
}
if __name__=='__main__':
    name=sys.argv[1]; seed=int(sys.argv[2]); tmax=float(sys.argv[3]); K=int(sys.argv[4]) if len(sys.argv)>4 else 6
    n,sets=SYS[name]; rng=random.Random(seed); base=sum(len(S)-1 for S in sets)
    stats={}; bad=[]; seen=set(); t0=time.time(); nchk=0
    c=honest(n,sets,rng); steps=0
    while time.time()-t0<tmax:
        steps+=1
        if steps%400==0: c=honest(n,sets,rng)
        c2=mutate(c,rng)
        if c2 is None or len(c2['gates'])>base+K: continue
        c=c2
        key=json.dumps(c['gates'])
        if key in seen: continue
        seen.add(key); nchk+=1
        T=tts(c); assert is_correct(c,T) and is_clean_live(c,T)
        summarize(stats,check(c),c,bad)
    pickle.dump((stats,bad,nchk),open(f'gen_{name}_{seed}.pkl','wb'))
    print(name,'seed',seed,'distinct circuits checked',nchk,'steps',steps)
    for k in sorted(stats): print(' %-18s instances %7d violations %4d min slack %s'%(k,*stats[k]))
    for b in bad[:4]: print('BAD',b[0],b[1],json.dumps(b[2]))
