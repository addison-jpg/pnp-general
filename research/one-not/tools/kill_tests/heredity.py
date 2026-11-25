# Kill tests asked by coord 11:42:
# (a) heredity step: for a family F of sets put x_v := 1 for every v outside V(F) (NOT gate kept).
#     (a1) restricted circuit correct for F; (a2) every valid I1 class of the restricted instance (zero point Z' with
#     h = 0, atoms {u}, all inside the subcube) equals a valid pure class of the ORIGINAL instance; restricted I0
#     classes are original I0 classes by definition (zero point top_w, atoms with h = 1), so only I1 is tested;
#     (a3) s_res (live gates after constant propagation) against base_F and against the gates in the restricted menus.
# (b) research: an I0 atom choice for u in S_w avoiding S_v exists  iff  h(not((S_w ∪ S_v) \ {u})) = 1.
import sys, os, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'research/one-not'
sys.argv=['x',ROOT,'10']
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
st=collections.Counter(); fails=[]; gaps=[]; bfail=[]
def live_count(n,G,outs_F,O):
    val={}                                   # wire -> ('c',bit) | ('w',wire)
    for v in range(n): val[v]=('c',1) if O>>v&1 else ('w',v)
    ins={}
    for k,g in enumerate(G):
        i=n+k; a=[val[j] for j in g[1:]]
        if g[0]=='not':
            val[i]=('c',1-a[0][1]) if a[0][0]=='c' else ('w',i); ins[i]=[a[0][1]] if a[0][0]=='w' else []
            continue
        absorb=0 if g[0]=='and' else 1
        if any(x==('c',absorb) for x in a): val[i]=('c',absorb); continue
        rest=sorted({x[1] for x in a if x[0]=='w'})
        if not rest: val[i]=('c',1-absorb)
        elif len(rest)==1: val[i]=('w',rest[0])
        else: val[i]=('w',i); ins[i]=rest
    seen=set(); stack=[val[o][1] for o in outs_F if val[o][0]=='w']
    while stack:
        i=stack.pop()
        if i in seen or i<n: continue
        seen.add(i); stack.extend(ins.get(i,[]))
    return len(seen)
for name,n,S,G,outs in circuits():
    if n>10 or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n; FULLV=P_-1
    osum=[functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for R in S]
    if any(Wr[o]!=t for o,t in zip(outs,osum)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    st['circuits']+=1
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    mint=[x for x in range(P_) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
    Sm=[sum(1<<u for u in R) for R in S]; top=[FULLV&~m for m in Sm]
    # (b)
    for w,v in itertools.permutations(range(len(S)),2):
        for u in S[w]:
            f=hb(FULLV&~((Sm[w]|Sm[v])&~(1<<u)))
            strict=any((m&Sm[w])&~(1<<u)==0 and (m&Sm[v])==0 for m in mint)
            loose=any((m&Sm[w])&~(1<<u)==0 and (m&Sm[v])&~(1<<u)==0 for m in mint)
            st['(b) triples']+=1; st['(b) formula = loose reading (m ∩ S_v ⊆ {u})']+=(bool(f)==loose)
            if u in S[v]: st['(b) u common: triples']+=1; st['(b) u common: formula = strict reading']+=(bool(f)==strict)
            else: st['(b) u not in S_v: formula = strict reading']+=(bool(f)==strict); st['(b) u not in S_v: triples']+=1
    # original valid I1 classes and minterm I0 classes
    A=[]; FULL={}
    for w,R in enumerate(S):
        rest=[x for x in range(n) if x not in R]; cls=set()
        for r in range(len(rest)+1):
            for zz in itertools.combinations(rest,r):
                z=sum(1<<x for x in zz)
                if not hb(z): cls.add(merges(W1,n,G,R,z,{u:1<<u for u in R}))
        per=[[m for m in mint if (m&Sm[w])&~(1<<u)==0] for u in R]
        if all(per):
            for ms in itertools.islice(itertools.product(*per),3000): cls.add(merges(W0,n,G,R,top[w],{u:ms[i]|1<<u for i,u in enumerate(R)}))
        A.append(cls)
    for r in range(2,len(S)+1):
        for F in itertools.combinations(range(len(S)),r):
            VF=functools.reduce(lambda a,b:a|b,[Sm[w] for w in F]); O=FULLV&~VF
            if O==0: continue
            st['(a) families with a proper restriction']+=1
            if hb(O): st['(a) NOT gate becomes constant (h = 1 on the subcube)']+=1
            menu=set(); baseF=sum(len(S[w])-1 for w in F)
            for w in F:
                R=S[w]; rest=[x for x in range(n) if (VF>>x&1) and x not in R]
                for q in range(len(rest)+1):
                    for zz in itertools.combinations(rest,q):
                        z=sum(1<<x for x in zz)|O
                        if hb(z): continue
                        M=merges(W1,n,G,R,z,{u:(1<<u)|O for u in R}); menu|=M; st['(a2) restricted I1 classes']+=1
                        if M in A[w]: st['(a2) equal to an original pure class']+=1; continue
                        if w not in FULL:
                            perf=[[m for m in range(P_) if hb(m) and (m&Sm[w])&~(1<<u)==0] for u in R]; size=1
                            for q_ in perf: size*=max(1,len(q_))
                            FULL[w]=None if (size>60000 or not all(perf)) and all(perf) else ({merges(W0,n,G,R,top[w],{u:ms[i]|1<<u for i,u in enumerate(R)}) for ms in itertools.product(*perf)} if all(perf) else set())
                        if FULL[w] is None: st['(a2) undetermined (original I0 menu too large to list)']+=1
                        elif M in FULL[w]: st['(a2) equal to an original pure class']+=1
                        else:
                            st['(a2) TRUE failures (full validity)']+=1; st['(a2) TRUE failures on a set of size >= 3']+=(len(R)>=3)
                            fails.append((len(R)<3,n,len(G),len(F),name.split('/')[-1],[S[x] for x in F],R,sorted(M)))
                mp=[x for x in range(P_) if (x&O)==0 and (x&~VF)==0 and hb(x|O) and not any(hb((x&~(1<<y))|O) for y in range(n) if x>>y&1)]
                per=[[m for m in mp if (m&Sm[w])&~(1<<u)==0] for u in R]
                if all(per):
                    for ms in itertools.islice(itertools.product(*per),500): menu|=merges(W0,n,G,R,top[w],{u:ms[i]|(1<<u)|O for i,u in enumerate(R)})
            sres=live_count(n,G,[outs[w] for w in F],O)
            gaps.append((sres-len(menu),sres-baseF,sres,len(menu),baseF,name.split('/')[-1],len(F)))
for k,v in sorted(st.items()): print('%-62s %d'%(k,v))
fails.sort(); print('(a2) TRUE FAILURES',len(fails),'(sorted: sets of size >= 3 first, then smallest)'); [print('   ',f[1:]) for f in fails[:5]]
if gaps:
    print('(a3) families',len(gaps),'| s_res <= #gates in restricted menus on',sum(1 for g in gaps if g[0]<=0),'| min(s_res - menu gates)',min(g[0] for g in gaps),'| min(s_res - base_F)',min(g[1] for g in gaps))
    print('   tightest',sorted(gaps)[:3])
