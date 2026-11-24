# MU by induction on points. UC = OR gates that, in one of the two monotone faces, are false at a valid zero point Z of
# some set w and true at Z + e_u for two u in S_w:
#   world 1: h(Z) = 0, tables of C_1;   world 0: h(Z + e_u) = 1 for every u in S_w, tables of C_0.
# (These are the count sets of the most general GM-valid pure systems; they contain every Lean-valid pure class.)
# Deleting a point v (x_v := 0) gives the instance S - v with base' = base - deg2(v). Heredity UC' ⊆ UC holds by
# construction. Question: is the gain |UC \ UC'_v| >= deg2(v)  (for every v? for some v?)
import sys, os, json, itertools, collections, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else '951'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
sys.argv=['x',ROOT,str(NMAX)]
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
def UC(n,G,W0,W1,hb,sets,dead=0):
    P_=1<<n; ors=[n+k for k,g in enumerate(G) if g[0]=='or']; out=set()
    for R in sets:
        if len(R)<2: continue
        Rm=sum(1<<u for u in R); free=(P_-1)&~Rm&~dead; Z=free
        while True:
            w1=not hb(Z); w0=all(hb(Z|1<<u) for u in R)
            if w1 or w0:
                for g in ors:
                    if g in out: continue
                    if w1 and not (W1[g]>>Z)&1 and sum((W1[g]>>(Z|1<<u))&1 for u in R)>=2: out.add(g)
                    elif w0 and not (W0[g]>>Z)&1 and sum((W0[g]>>(Z|1<<u))&1 for u in R)>=2: out.add(g)
            if Z==0: break
            Z=(Z-1)&free
    return out
st=collections.Counter(); slack=collections.Counter(); worst=[]
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1)
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    ni=n+[k for k,g in enumerate(G) if g[0]=='not'][0]; h=Wr[G[ni-n][1]]; hb=lambda x:(h>>x)&1
    base=sum(len(R)-1 for R in S); U=UC(n,G,W0,W1,hb,S); st['circuits']+=1
    slack[min(len(U)-base,9)]+=1; st['MU holds (|UC| >= base)']+=(len(U)>=base)
    pts=sorted({u for R in S for u in R}); allv=True; somev=False; gains=[]
    for v in pts:
        S2=[[u for u in R if u!=v] for R in S]; deg=sum(1 for R in S if v in R and len(R)>=2)
        U2=UC(n,G,W0,W1,hb,S2,dead=1<<v)
        if not U2<=U: st['HEREDITY FAILS (UC\' not inside UC)']+=1
        g=len(U-U2); gains.append((g-deg,v,g,deg)); st['points']+=1; st['points with gain >= deg']+=(g>=deg)
        allv&=(g>=deg); somev|=(g>=deg)
    st['circuits: gain >= deg at EVERY point']+=allv; st['circuits: gain >= deg at SOME point']+=somev
    if not allv: worst.append((min(gains)[0],name.split('/')[-1],[x for x in sorted(gains)[:3]],len(S),s_:=len(G),base))
for k,v in sorted(st.items()): print('%-46s %d'%(k,v))
print('slack |UC| - base:',' '.join('%s:%d'%(('9+' if k==9 else k),slack[k]) for k in sorted(slack)))
worst.sort(); print('worst (gain-deg, circuit, [(gain-deg, v, gain, deg)], #sets, #gates, base):'); [print('  ',w) for w in worst[:6]]
