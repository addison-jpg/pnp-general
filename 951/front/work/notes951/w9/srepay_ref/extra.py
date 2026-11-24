import random, json, itertools, collections
from ref import check, UF, tts
from adv import Bld, shuffle_topo
rng=random.Random(7)
# (1) generalised H5: k disjoint m-sets (hyperforest), h=Th2, column ORs first -> coll=(k-1)(m-1)
def genH5(k,m,order_cols_first=True):
    n=k*m; b=Bld(n); sets=[[w*m+i for i in range(m)] for w in range(k)]
    cols=[]
    for i in range(m):
        c=sets[0][i]
        for w in range(1,k): c=b.g('or',c,sets[w][i])
        cols.append(c)
    ALL=cols[0]
    for c in cols[1:]: ALL=b.g('or',ALL,c)
    # Th2
    o=0; t=None
    for v in range(1,n):
        a=b.g('and',o,v); t=a if t is None else b.g('or',t,a); o=b.g('or',o,v)
    h=t; N=b.g('not',h); outs=[]
    for S in sets:
        R=S[0]
        for u in S[1:]: R=b.g('or',R,u)
        outs.append(b.g('or',b.g('and',b.g('and',ALL,N),b.g('or',R,h)),b.g('and',R,h)))
    return dict(n=n,sets=sets,gates=b.G,outs=outs)
for k,m in [(2,4),(2,5),(3,3),(3,4),(4,3),(5,2),(2,6)]:
    c=genH5(k,m); r,v=check(c)
    print('genH5',k,m,{x:r[x] for x in ('correct','ess','s','base','cyc','J','need','coll','X','nonj','out','kmax')},'VIOL' if v else 'ok', 'coll==(k-1)(m-1):',r['coll']==(k-1)*(m-1))
# (2) two intersecting sets (hyperforest), double merge whose child is an INPUT x_u, u in both sets
# S_a={0,1,2}, S_b={0,3,4}; t=x1|x3 (cross merge, in X), g=x0|t (double merge, child x0 is an input)
def inter():
    n=5; b=Bld(n); Sa=[0,1,2]; Sb=[0,3,4]
    t=b.g('or',1,3); g=b.g('or',0,t); P=b.g('or',g,2); P=b.g('or',P,4)     # OR of all 5
    o=0; th=None
    for v in range(1,n):
        a=b.g('and',o,v); th=a if th is None else b.g('or',th,a); o=b.g('or',o,v)
    h=th; N=b.g('not',h); outs=[]
    for S in (Sa,Sb):
        R=b.g('or',b.g('or',S[0],S[1]),S[2])
        outs.append(b.g('or',b.g('and',b.g('and',P,N),b.g('or',R,h)),b.g('and',R,h)))
    return dict(n=n,sets=[Sa,Sb],gates=b.G,outs=outs)
c=inter(); r,v=check(c); print('inter',r,'VIOL' if v else 'ok'); json.dump(c,open('inter_input_child.json','w'))
# (3) abstract Lemma J: random monotone circuits over (x,y) (not correct for anything); outputs = random gates vanishing at (0,1);
#     S_w := any subset (size>=2) of B(F_w).  Claim: #joint OR merges >= |V'|-c, per-set merges = d_w exactly, CHARGE.
def abstract(trials=20000):
    bad=0; tot=0
    for _ in range(trials):
        n=rng.randint(3,7); y=n; m=rng.randint(4,25); val0=[1<<v for v in range(n)]  # value on atoms: bitmask over units; plus val at 0
        # wire = (value at (0,1), set of units where 1 at (e_u,1)) ; monotone so at0=1 => all units
        wires=[(0,frozenset([v])) for v in range(n)]+[(1,frozenset(range(n)))]
        G=[]
        for k in range(m):
            a,b=rng.randrange(len(wires)),rng.randrange(len(wires)); op=rng.choice(['and','or','or'])
            (za,Ba),(zb,Bb)=wires[a],wires[b]
            wires.append((za&zb,Ba&Bb) if op=='and' else (za|zb,Ba|Bb)); G.append((op,a,b))
        cand=[n+1+k for k in range(m) if wires[n+1+k][0]==0 and len(wires[n+1+k][1])>=2]
        if not cand: continue
        outs=rng.sample(cand,min(len(cand),rng.randint(1,4))); S=[sorted(rng.sample(sorted(wires[o][1]),rng.randint(2,len(wires[o][1])))) for o in outs]
        Vp=sorted({u for s in S for u in s}); hu=UF(Vp)
        for s in S:
            for u in s[1:]: hu.u(s[0],u)
        comp=hu.nb(); base=sum(len(s)-1 for s in S)
        ju=UF(Vp); su=[UF(s) for s in S]; J=0; M=[set() for _ in S]
        for k,(op,a,b) in enumerate(G):
            gid=n+1+k
            if wires[gid][0] or op!='or': continue
            Ba=[u for u in wires[a][1] if u in Vp]; Bb=[u for u in wires[b][1] if u in Vp]
            if Ba and Bb and ju.u(Ba[0],Bb[0]): J+=1
            for wi,s in enumerate(S):
                a_=[u for u in Ba if u in s]; b_=[u for u in Bb if u in s]
                if a_ and b_ and su[wi].u(a_[0],b_[0]): M[wi].add(gid)
        tot+=1
        if J<len(Vp)-comp or any(len(M[i])!=len(S[i])-1 for i in range(len(S))) or ju.nb()>comp: bad+=1
    print('abstract Lemma J: trials',tot,'violations',bad)
abstract()
# (4) two-set cut formula: maxflow=min(base,|U|)
def mf(dem,cls):
    owner={}
    def aug(w,seen):
        for g in cls[w]:
            if g in seen: continue
            seen.add(g)
            if g not in owner or aug(owner[g],seen): owner[g]=w; return True
        return False
    return sum(1 for w in range(len(dem)) for _ in range(dem[w]) if aug(w,set()))
bad=0
for _ in range(20000):
    da,db=rng.randint(1,5),rng.randint(1,5); U=list(range(14))
    A=set(rng.sample(U,rng.randint(da,10))); Bc=set(rng.sample(U,rng.randint(db,10)))
    if mf([da,db],[sorted(A),sorted(Bc)])!=min(da+db,len(A|Bc)): bad+=1
print('two-set maxflow=min(base,|U|): violations',bad)
# (5) three sets on a hyperforest: is V1 (def<=out) automatic for arbitrary classes with |cl_w|>=d_w? abstract counterexample to "every choice" beyond 2 sets
da=db=dc=2; s1=7  # M has s-1=7 gates >= base 6
cl=[[0,1],[0,1],list(range(7))]; fl=mf([2,2,2],cl); U=7; print('3 sets abstract: base 6, s-1=7, |U|=7, maxflow',fl,'def',6-fl,'out',s1-U,'=> V1 fails for such a (hypothetical) choice')
