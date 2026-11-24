# PureSDR as a binary CSP (coord 11:46): one variable per set, domain = its valid pure classes, constraint = disjoint.
# Validity as in Lean, with the widened I1:  I1: Z with h(Z) = 0, Z ∩ S_w = ∅, atoms {u} ∪ A, A ⊆ Z (tables of C_1);
#                                            I0: zero point top_w, atoms m_u ∪ {u}, h(m_u) = 1, m_u ∩ S_w ⊆ {u} (tables of C_0).
# Sets with h(top_w) = 0 are fixed at their free class K_1(w) (C_1, zero point top_w, atoms e_u).
import sys, os, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
sys.argv=['x',ROOT,str(NMAX)]
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
big=[]; st=collections.Counter(); H0=collections.Counter(); H1=collections.Counter(); H2=collections.Counter(); notes=[]
def subsets(mask):
    s=mask
    while True:
        yield s
        if s==0: return
        s=(s-1)&mask
def ac3(dom,vars_):
    changed=True
    while changed:
        changed=False
        for a in vars_:
            for b in vars_:
                if a==b: continue
                keep=[x for x in dom[a] if any(not (x&y) for y in dom[b])]
                if len(keep)!=len(dom[a]): dom[a]=keep; changed=True
                if not keep: return False
    return True
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n; FULLV=P_-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    st['circuits']+=1
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    Sm=[sum(1<<u for u in R) for R in S]; top=[FULLV&~m for m in Sm]; m_=len(S)
    typeA=[bool(hb(top[w])) for w in range(m_)]; dom={}; capped=False
    for w,R in enumerate(S):
        cls=set()
        for Z in subsets(top[w]):
            if hb(Z): continue
            for A in subsets(Z): cls.add(merges(W1,n,G,R,Z,{u:(1<<u)|A for u in R}))
        per=[[m for m in range(P_) if hb(m) and (m&Sm[w])&~(1<<u)==0] for u in R]
        if all(per):
            size=1
            for q in per: size*=len(q)
            if size>20000:
                capped=True; mint=[x for x in range(P_) if hb(x) and not any(hb(x&~(1<<v)) for v in range(n) if x>>v&1)]
                per=[[m for m in mint if (m&Sm[w])&~(1<<u)==0] for u in R]
            for ms in itertools.islice(itertools.product(*per),20000): cls.add(merges(W0,n,G,R,top[w],{u:ms[i]|1<<u for i,u in enumerate(R)}))
        dom[w]=list(cls); H0[min(len(cls),9)]+=1
    st['circuits with a capped I0 menu']+=capped
    fixed={w:merges(W1,n,G,S[w],top[w],{u:1<<u for u in S[w]}) for w in range(m_) if not typeA[w]}
    if any(fixed[a]&fixed[b] for a,b in itertools.combinations(fixed,2)): st['free classes at top_w collide (should be 0)']+=1
    used=frozenset().union(*fixed.values()) if fixed else frozenset()
    A=[w for w in range(m_) if typeA[w]]; st['type-A sets']+=len(A); st['sets fixed at their free class']+=len(fixed)
    d1={w:[x for x in dom[w] if not (x&used)] for w in A}
    for w in A: H1[min(len(d1[w]),9)]+=1
    if not A: st['circuits with no type-A set']+=1; continue
    before={w:len(d1[w]) for w in A}; d2={w:list(d1[w]) for w in A}
    if not ac3(d2,A):
        st['arc consistency empties a domain (free classes must be re-picked)']+=1; notes.append(name.split('/')[-1]); continue
    for w in A:
        H2[min(len(d2[w]),9)]+=1
        if len(d2[w])==1 and before[w]>1: st['forced by arc consistency: largest domain before']=max(st['forced by arc consistency: largest domain before'],before[w])
        if len(d2[w])<before[w]: st['sets pruned by arc consistency']+=1
    st['circuits: all type-A domains of size 1 after AC']+=all(len(d2[w])==1 for w in A)
    st['circuits: all type-A domains of size <= 2 after AC']+=all(len(d2[w])<=2 for w in A)
    st['circuits: every class of every type-A set is one gate (matching)']+=all(len(x)==1 for w in A for x in d2[w])
    # search with arc consistency maintained; count dead ends
    dead=[0]
    def solve(d,todo):
        if not todo: return True
        w=min(todo,key=lambda v:len(d[v]))
        for x in d[w]:
            e={v:list(d[v]) for v in todo if v!=w}
            for v in e: e[v]=[y for y in e[v] if not (y&x)]
            rest=[v for v in todo if v!=w]
            if all(e[v] for v in rest) and (not rest or ac3(e,rest)) and solve(e,rest): return True
            dead[0]+=1
        return False
    ok=solve(d2,A); st['solved']+=ok; st['solved with no dead end after AC']+=(ok and dead[0]==0)
    st['max dead ends']=max(st['max dead ends'],dead[0])
    # is every arc-consistent value part of a solution? (global consistency)
    glob=True
    for w in A:
        for x in d2[w]:
            e={v:[y for y in d2[v] if not (y&x)] for v in A if v!=w}; rest=[v for v in A if v!=w]
            if not (all(e[v] for v in rest) and (not rest or ac3(e,rest)) and solve(e,rest)): glob=False
    st['circuits where every arc-consistent value extends to a solution']+=glob
    if not glob: notes.append('NOT-GLOBAL '+name.split('/')[-1]+' sets '+str([S[w] for w in A])+' domains '+str([len(d2[w]) for w in A]))
    if any(len(d2[w])>2 for w in A): big.append((max(len(d2[w]) for w in A),name.split('/')[-1],max(len(R) for R in S)))
for k,v in sorted(st.items()): print('%-72s %d'%(k,v))
f=lambda H:' '.join('%s:%d'%(('9+' if k==9 else k),H[k]) for k in sorted(H))
print('domain sizes, all sets, full menu      ',f(H0)); print('type-A domains after fixing free classes',f(H1)); print('type-A domains after arc consistency   ',f(H2))
print('notes:',notes[:6]); big.sort(reverse=True); print('largest post-AC domains (size, circuit, largest set):',big[:8]); print('circuits with a domain > 2:',len(big),'of which graph systems (largest set 2):',sum(1 for b in big if b[2]==2))
