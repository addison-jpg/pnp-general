# Which processing orders of the sets make EVERY partial disjoint choice extendable to the next set?
# (If one natural order always works, the existence proof is a one-set induction, with no augmenting.)
import sys, json, itertools, collections
sys.argv=['x',sys.argv[1] if len(sys.argv)>1 else 'one-not','10']
src=open('canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
st=collections.Counter(); bad=collections.defaultdict(list); tot=0
for name,n,S,G,outs in circuits():
    if n>10 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); P_=1<<n
    import functools
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    tot+=1
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    opts=[]
    for w,R in enumerate(S):
        rest=[v for v in range(n) if v not in R]
        o=[merges(Wr,n,G,R,z,{u:z|1<<u for u in R}) for z in (sum(1<<v for v in zz) for r in range(len(rest)+1) for zz in itertools.combinations(rest,r))]
        opts.append(list(dict.fromkeys(o)))
    m=len(S); heavy=[any(hb(1<<u) for u in R) for R in S]
    univ=[frozenset.intersection(*opts[w]) for w in range(m)]
    orders={'output position, early first':sorted(range(m),key=lambda w:outs[w]),
            'output position, late first':sorted(range(m),key=lambda w:-outs[w]),
            'fewest options first':sorted(range(m),key=lambda w:(len(opts[w]),w)),
            'most options first':sorted(range(m),key=lambda w:(-len(opts[w]),w)),
            'heavy sets last':sorted(range(m),key=lambda w:(heavy[w],len(opts[w]),w)),
            'heavy sets first':sorted(range(m),key=lambda w:(not heavy[w],len(opts[w]),w)),
            'most universal merges first':sorted(range(m),key=lambda w:(-len(univ[w]),w))}
    for on,order in orders.items():
        ok=True; states=[frozenset()]
        for w in order:
            nxt=set()
            for used in states:
                ext=[used|M for M in opts[w] if not (M&used)]
                if not ext: ok=False; break
                nxt.update(ext)
            if not ok: break
            states=list(nxt)
            if len(states)>20000: states=states[:20000]
        st[on]+=ok
        if not ok: bad[on].append(name.split('/')[-1])
    # weaker: SOME order is universally extendable
print('circuits',tot)
for k,v in sorted(st.items(),key=lambda kv:-kv[1]): print('%-32s every partial choice extends on %d / %d'%(k,v,tot))
for k,v in bad.items(): print('FAIL',k,len(v),v[:10])
