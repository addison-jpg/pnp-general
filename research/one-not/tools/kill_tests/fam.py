# Kill test for research/one-not/PROOF_PLAN_SUGGESTIONS.md: lemmas W0, W1, X and the canonical start.
import sys, glob, json, itertools, collections
ROOT=sys.argv[1]; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 11
def circuits():
    seen=set()
    for f in sorted(glob.glob(ROOT+'/**/*.json',recursive=True))+sorted(glob.glob(ROOT+'/**/*.jsonl',recursive=True)):
        try:
            if f.endswith('.jsonl'): items=[json.loads(l) for l in open(f) if l.strip()]
            else:
                d=json.load(open(f)); items=d if isinstance(d,list) else [d]
        except Exception: continue
        for i,c in enumerate(items):
            if not (isinstance(c,dict) and all(k in c for k in ('n','sets','gates','outs'))): continue
            try:
                G=[[g[0]]+[int(x) for x in g[1:]] for g in c['gates']]
                key=json.dumps([c['n'],c['sets'],G,c['outs']])
            except Exception: continue
            if key in seen: continue
            seen.add(key); yield f.replace(ROOT+'/','')+':%d'%i, c['n'], [list(s) for s in c['sets']], G, list(c['outs'])
def tables(n,G,mode):
    P=1<<n; FULL=(1<<P)-1; W=[]
    for v in range(n):
        m=0
        for x in range(P):
            if x>>v&1: m|=1<<x
        W.append(m)
    for g in G:
        if g[0]=='not': W.append((FULL^W[g[1]]) if mode=='real' else (0 if mode==0 else FULL))
        elif g[0]=='and': W.append(W[g[1]]&W[g[2]])
        elif g[0]=='or': W.append(W[g[1]]|W[g[2]])
        else: raise ValueError(g[0])
    return W
def merges(W,n,G,R,Z,P):
    # union-find run of Lemma M for the test system (zero point Z, atom points P[u]) on wire tables W
    par={u:u for u in R}
    def find(u):
        while par[u]!=u: par[u]=par[par[u]]; u=par[u]
        return u
    B={}
    for v in range(n):
        if not (W[v]>>Z)&1: B[v]=frozenset(u for u in R if (W[v]>>P[u])&1)
    M=[]
    for k,g in enumerate(G):
        i=n+k
        if (W[i]>>Z)&1: continue
        B[i]=frozenset(u for u in R if (W[i]>>P[u])&1)
        if g[0]=='or':
            a=B.get(g[1],frozenset()); b=B.get(g[2],frozenset())
            if a and b:
                ra,rb=find(next(iter(a))),find(next(iter(b)))
                if ra!=rb: par[ra]=rb; M.append(i)
    return frozenset(M)
def kclass(W,n,G,R,Z,P):
    return frozenset(n+k for k,g in enumerate(G) if g[0]=='or' and not (W[n+k]>>Z)&1 and sum((W[n+k]>>P[u])&1 for u in R)>=2)
def sdr(opts):
    order=sorted(range(len(opts)),key=lambda w:len(opts[w]))
    def rec(i,used):
        if i==len(order): return True
        for o in opts[order[i]]:
            if not (o&used) and rec(i+1,used|o): return True
        return False
    return rec(0,frozenset())
st=collections.Counter(); bad=collections.defaultdict(list)
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: st['skipped']+=1; continue
    try: Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1)
    except Exception: st['skipped']+=1; continue
    P_=1<<n; var=Wr[:n]
    if any(Wr[o]!=__import__('functools').reduce(lambda a,b:a|b,[var[u] for u in R],0) for o,R in zip(outs,S)): st['incorrect']+=1; continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): st['not (1,1)-disjoint']+=1; continue
    st['circuits']+=1
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    mint=[x for x in range(P_) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
    mint.sort(key=lambda x:(bin(x).count('1'),x))
    top=[(P_-1)&~sum(1<<u for u in R) for R in S]; d=[len(R)-1 for R in S]
    O0=[];O1=[];OP=[];typ=[]
    for w,R in enumerate(S):
        heavy=[u for u in R if hb(1<<u)]; rest=[v for v in range(n) if v not in R]
        typ.append('A' if hb(top[w]) else ('B' if not heavy else 'S'))
        o0=[merges(W0,n,G,R,top[w],{u:m|1<<u for u in R}) for m in mint if not any(m>>u&1 for u in R)] if hb(top[w]) else []
        zs=[sum(1<<v for v in zz) for r in range(len(rest)+1) for zz in itertools.combinations(rest,r)]
        o1=[]
        if not heavy:
            for z in zs:
                if hb(z): continue
                if all(hb(z|1<<v) for v in rest if not z>>v&1):   # maximal zero point inside D
                    o1.append(merges(W1,n,G,R,z,{u:1<<u for u in R}))
        op=[merges(Wr,n,G,R,z,{u:z|1<<u for u in R}) for z in zs]
        for nm,L in (('O0',o0),('O1',o1),('OP',op)):
            if any(len(M)!=d[w] for M in L): bad['size '+nm].append((name,w))
        O0.append(list(dict.fromkeys(o0))); O1.append(list(dict.fromkeys(o1))); OP.append(list(dict.fromkeys(op)))
    fams={'F0 world-0 interval only':[O0[w] for w in range(len(S))],
          'F1 world-0 + world-1 interval':[list(dict.fromkeys(O0[w]+O1[w])) for w in range(len(S))],
          'F2 F1 + plain points for split sets':[list(dict.fromkeys(O0[w]+O1[w]+(OP[w] if typ[w]=='S' else []))) for w in range(len(S))],
          'F3 plain zero points only (MergeSDR)':OP,
          'F4 everything':[list(dict.fromkeys(O0[w]+O1[w]+OP[w])) for w in range(len(S))]}
    st['circuits with a split set']+=('S' in typ)
    for fn,opts in fams.items():
        ok=all(opts) and sdr(opts); st[fn+': SDR']+=ok
        if not ok: bad[fn].append(name.split('/')[-1])
for k,v in sorted(st.items()): print('%-34s %d'%(k,v))
for k,v in bad.items(): print('FAIL',k,len(v),v[:14])
