import sys, json, itertools
sys.argv=['x',sys.argv[1] if len(sys.argv)>1 else '951','10']
src=open('canon.py').read(); exec(src[:src.index("st=collections.Counter()")])
def load(f):
    c=json.load(open(f)); c=c[0] if isinstance(c,list) else c
    return c['n'],[list(s) for s in c['sets']],[[g[0]]+[int(x) for x in g[1:]] for g in c['gates']],list(c['outs'])
for f in sys.stdin.read().split():
    n,S,G,outs=load(f); Wr=tables(n,G,'real'); P_=1<<n
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    mint=[x for x in range(P_) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
    bits=lambda x:[v for v in range(n) if x>>v&1]
    print('==',f.split('/')[-1],'n',n,'gates',len(G),'sets',S,'h minterms',[bits(m) for m in mint])
    def world(R,z):
        if hb(z): return 'W0'
        return 'W1' if all(not hb(z|1<<u) for u in R) else 'MIX'
    opts=[]
    for w,R in enumerate(S):
        rest=[v for v in range(n) if v not in R]; by={}
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<v for v in zz); M=merges(Wr,n,G,R,z,{u:z|1<<u for u in R}); by.setdefault(M,[]).append(z)
        opts.append(by)
        top=(P_-1)&~sum(1<<u for u in R)
        print('  set',w,R,'type','A' if hb(top) else 'B/S','heavy',[u for u in R if hb(1<<u)],'#distinct merge sets',len(by),
              'worlds available',sorted({world(R,z) for zs in by.values() for z in zs}))
    sols=[]
    def rec(i,used,pick):
        if len(sols)>=4000: return
        if i==len(S): sols.append(list(pick)); return
        for M in opts[i]:
            if not (M&used): pick.append(M); rec(i+1,used|M,pick); pick.pop()
    rec(0,frozenset(),[])
    print('  #SDR solutions (capped 4000):',len(sols))
    pat={}
    for sol in sols:
        key=tuple('/'.join(sorted({world(S[w],z) for z in opts[w][M]})) for w,M in enumerate(sol)); pat[key]=pat.get(key,0)+1
    for k,v in sorted(pat.items(),key=lambda kv:-kv[1])[:8]: print('   worlds per set',k,'x',v)
    if sols:
        sol=sols[0]
        for w,M in enumerate(sol):
            zs=opts[w][M]; print('   e.g. set',w,'merge gates',sorted(M),'zero points',[bits(z) for z in zs[:4]],'of',len(zs))
