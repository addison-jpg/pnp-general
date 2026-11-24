# STAR-SEP (front A2; Lean: one-not/lean/PEqualNP/W951/PureStar.lean, StarSep gates p S Q), tested as defined there.
#   alive(Q) = sets avoiding Q;  star(Q, v) = alive sets through v.
#   Menu_Q(w):  I1 (oneAt Z A): Z ∩ S_w = ∅, h(Z) = 0, atoms {u} ∪ R' with ONE R', Q ⊆ R' ⊆ Z  (tables of C_1);
#               I0 (zero m):    zero point top_w, atoms m_u ∪ {u}, h(m_u) = 1, m_u ∩ S_w ⊆ {u}, Q ⊆ m_u (tables of C_0).
#   StarSep(Q): no alive set, or some v with nonempty star and classes K_w ∈ Menu_Q(w) (w in the star), pairwise
#   disjoint, each disjoint from EVERY class of Menu_{Q ∪ {v}}(w') for every alive w' not through v.
import sys, os, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 8
sys.argv=['x',ROOT,str(NMAX)]
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
def subsets(mask):
    s=mask
    while True:
        yield s
        if s==0: return
        s=(s-1)&mask
st=collections.Counter(); fails=[]; vstat=collections.Counter()
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n; FULLV=P_-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    Sm=[sum(1<<u for u in R) for R in S]; top=[FULLV&~m for m in Sm]; M=len(S); exact=True
    one=[collections.defaultdict(set) for _ in S]; zer=[None]*M
    for w,R in enumerate(S):
        for Z in subsets(top[w]):
            if hb(Z): continue
            for Rp in subsets(Z): one[w][merges(W1,n,G,R,Z,{u:(1<<u)|Rp for u in R})].add(Rp)
        per=[]
        for u in R:
            sig=collections.defaultdict(list)
            for m in range(P_):
                if hb(m) and (m&Sm[w])&~(1<<u)==0:
                    p=m|1<<u; sig[tuple((W0[i]>>p)&1 for i in range(n,n+len(G)))].append(m)
            per.append(list(sig.items()))
        size=1
        for q in per: size*=len(q)
        if size>60000: exact=False; zer[w]=(per,None); continue
        cls={}
        if all(per):
            for combo in itertools.product(*[range(len(q)) for q in per]):
                cls[combo]=merges(W0,n,G,R,top[w],{u:per[i][combo[i]][1][0]|1<<u for i,u in enumerate(R)})
        zer[w]=(per,cls)
    if not exact: st['skipped: I0 menu too large to list exactly']+=1; continue
    st['circuits']+=1; cache={}
    def menu(w,Q):
        k=(w,Q)
        if k in cache: return cache[k]
        out={c for c,ms in one[w].items() if any(Q&~Rp==0 for Rp in ms)}
        per,cls=zer[w]
        if cls:
            ok=[[i for i,(sg,ms) in enumerate(q) if any(Q&~m==0 for m in ms)] for q in per]
            if all(ok):
                for combo in itertools.product(*ok): out.add(cls[combo])
        cache[k]=out; return out
    def works(Q,v):
        alive=[w for w in range(M) if not Sm[w]&Q]; star=[w for w in alive if Sm[w]>>v&1]
        if not star: return None
        F=frozenset().union(*[c for w2 in alive if not Sm[w2]>>v&1 for c in menu(w2,Q|1<<v)]) if any(not Sm[w2]>>v&1 for w2 in alive) else frozenset()
        opts=[[c for c in menu(w,Q) if not (c&F)] for w in star]
        return all(opts) and sdr(opts)
    var=functools.reduce(lambda a,b:a|b,Sm); okall=True; firstbad=None
    for Q in sorted(subsets(var),key=lambda q:(bin(q).count('1'),q)):
        alive=[w for w in range(M) if not Sm[w]&Q]
        if not alive: continue
        st['(circuit, Q) pairs with an alive set']+=1
        res=[(v,works(Q,v)) for v in range(n) if any(Sm[w]>>v&1 for w in alive)]
        good=[v for v,r in res if r]
        vstat['working fraction of candidate v, bucket %d/4'%min(4,(4*len(good))//max(1,len(res)))]+=1
        if good: st['StarSep holds']+=1
        else:
            okall=False
            if firstbad is None: firstbad=Q
    st['circuits with StarSep for EVERY Q']+=okall
    # reachable Q: start at 0, add any working v
    seen={0}; todo=[0]; reach_ok=True
    while todo:
        Q=todo.pop(); alive=[w for w in range(M) if not Sm[w]&Q]
        if not alive: continue
        good=[v for v in range(n) if any(Sm[w]>>v&1 for w in alive) and works(Q,v)]
        if not good: reach_ok=False
        for v in good:
            if Q|1<<v not in seen: seen.add(Q|1<<v); todo.append(Q|1<<v)
    st['circuits with StarSep for every REACHABLE Q']+=reach_ok
    if not okall: fails.append((bin(firstbad).count('1'),n,len(G),name.split('/')[-1],[v for v in range(n) if firstbad>>v&1],S,reach_ok))
for k,v in sorted(st.items()): print('%-52s %d'%(k,v))
for k,v in sorted(vstat.items()): print('%-52s %d'%(k,v))
fails.sort(); print('FAILURES (|Q|, n, gates, circuit, Q, sets, reachable-ok):',len(fails)); [print('  ',f) for f in fails[:6]]
