# MU by induction on points, both moves, on every restricted sub-instance (D = points fixed to 0, Q = points fixed to 1).
# UC(D,Q) = count-set union, restriction-closed: OR gates g with a pair a,b of one alive set w (S_w ∩ Q = ∅, a,b ∉ D) and
# a zero point Z (Q ⊆ Z, Z ∩ (D ∪ S_w) = ∅) such that  world 1: h(Z)=0, C_1(g)(Z)=0, C_1(g)(Z+e_a)=C_1(g)(Z+e_b)=1,
# or world 0: C_0(g)(Z)=0, h(Z+e_a)=h(Z+e_b)=1, C_0(g)(Z+e_a)=C_0(g)(Z+e_b)=1.   UC(D+v,Q), UC(D,Q+v) ⊆ UC(D,Q) by construction.
# Run: python3 -I 951/tools/kill_tests/mu_light.py 951 9
import sys, os, itertools, collections, functools, random
ROOT=sys.argv[1] if len(sys.argv)>1 else '951'; NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
sys.argv=['x',ROOT,str(NMAX)]
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
def mk(name,n,S,G,outs):
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n; FULL=(1<<P_)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): return None
    h=Wr[[g for g in G if g[0]=='not'][0][1]]; X=W0[:n]; pw={}
    for k,g in enumerate(G):
        if g[0]!='or': continue
        i=n+k; L=[]
        for R in S:
            av=FULL
            for u in R: av&=FULL^X[u]
            for a,b in itertools.combinations(R,2):
                sa=1<<a; sb=1<<b
                M=((FULL^W1[i])&(W1[i]>>sa)&(W1[i]>>sb)&av&(FULL^h))|((FULL^W0[i])&(W0[i]>>sa)&(W0[i]>>sb)&av&(h>>sa)&(h>>sb))
                if M: L.append((a,b,M))
        pw[i]=L
    return dict(name=name,n=n,S=S,G=G,h=h,X=X,FULL=FULL,pw=pw,W0=W0)
def cube(c,D,Q):
    m=c['FULL']
    for v in range(c['n']):
        if Q>>v&1: m&=c['X'][v]
        elif D>>v&1: m&=c['FULL']^c['X'][v]
    return m
def UC(c,D=0,Q=0):
    cb=cube(c,D,Q); return {g for g,L in c['pw'].items() if any(not (D>>a|D>>b)&1 and M&cb for a,b,M in L)}
def alive(c,D,Q): return [R for R in c['S'] if not any(Q>>u&1 for u in R) and sum(1 for u in R if not D>>u&1)>=2]
def base(c,D=0,Q=0): return sum(sum(1 for u in R if not D>>u&1)-1 for R in alive(c,D,Q))
def apts(c,D=0,Q=0): return sorted({u for R in alive(c,D,Q) for u in R if not D>>u&1})
def infl(c,D,Q,v): return bin(((c['h']>>(1<<v))^c['h'])&cube(c,D,Q)&(c['FULL']^c['X'][v])).count('1')
random.seed(1); CS=[]
for name,n,S,G,outs in circuits():
    if n>NMAX or sum(1 for g in G if g[0]=='not')!=1 or len(S)<2: continue
    if any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) or any(len(R)<2 for R in S): continue
    c=mk(name.split('/')[-1],n,S,G,outs)
    if c: CS.append(c)
ncorp=len(CS)
# two hand-built monotone circuits with an unused NOT gate
lines=[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]]; last=(0,3,5,1,4,6,2); G=[['and',0,1],['and',7,2],['not',8]]; outs=[]
for L,l in zip(lines,last):
    a,b=[u for u in L if u!=l]; G.append(['or',a,b]); G.append(['or',7+len(G)-1,l]); outs.append(7+len(G)-1)
FANO=mk('FANO-FORMULA',7,lines,G,outs); CS.append(FANO)
JUNK=mk('JUNK',5,[[0,1,2],[1,3],[2,4]],[['and',0,3],['and',0,4],['not',5],['or',1,5],['or',2,6],['or',8,9],['or',10,0],['or',1,3],['or',2,4]],[11,12,13]); CS.append(JUNK)
for c in (FANO,JUNK):
    U=UC(c); b=base(c); print(c['name'],'|UC|',len(U),'base',b,' (v, gain0/deg, gain1/cost1):',[(v,'%d/%d'%(len(U-UC(c,1<<v,0)),b-base(c,1<<v,0)),'%d/%d'%(len(U-UC(c,0,1<<v)),b-base(c,0,1<<v))) for v in apts(c)])
st=collections.Counter(); bad=collections.defaultdict(list)
for c in CS:
    n=c['n']; pairs=[(D,Q) for Q in range(1<<n) for D in range(1<<n) if not D&Q]
    if len(pairs)>2500: pairs=[(0,0)]+random.sample(pairs,2500)
    for D,Q in pairs:
        P=apts(c,D,Q)
        if not P: continue
        cb=cube(c,D,Q); hh=c['h']&cb
        kind='h const' if hh in (0,cb) else ('heavy' if any((c['h']>>(Q|1<<v))&1 for v in P) else 'light')
        U=UC(c,D,Q); b=base(c,D,Q); st[kind+': instances']+=1; st[kind+': MU holds']+=(len(U)>=b)
        ok1={v:len(U-UC(c,D,Q|1<<v))>=b-base(c,D,Q|1<<v) for v in P}; ok0={v:len(U-UC(c,D|1<<v,Q))>=b-base(c,D|1<<v,Q) for v in P}
        st[kind+': x:=1 good at EVERY alive point']+=all(ok1.values()); st[kind+': x:=1 good at SOME alive point']+=any(ok1.values())
        st[kind+': x:=0 good at EVERY alive point']+=all(ok0.values()); st[kind+': x:=0 good at SOME alive point']+=any(ok0.values())
        if not any(ok0.values()): bad[kind+': x:=0 has NO good point'].append((c['name'],D,Q))
        if kind=='heavy':
            for v in P:
                if (c['h']>>(Q|1<<v))&1: st['heavy v: x:=1 tried']+=1; st['heavy v: x:=1 good']+=ok1[v]
        if kind=='light':
            st['light: points']+=len(P); st['light: points good for x:=1']+=sum(ok1.values())
            v=min(P,key=lambda v:(infl(c,D,Q,v),v)); st['light: rule "least h-influence" picks a good point']+=ok1[v]
            st['light: lemma C0 (UC gates with C_0(g)(Q+v)=1 >= cost) at some v']+=any(sum((c['W0'][g]>>(Q|1<<v))&1 for g in U)>=b-base(c,D,Q|1<<v) for v in P)
            for v in P:
                if not ok1[v]: bad['light: bad points for x:=1'].append((c['name'],D,Q,v))
print('corpus circuits',ncorp,'+ 2 hand-built')
for k,v in sorted(st.items()): print('%-66s %d'%(k,v))
for k,v in bad.items(): print(k,len(v),v[:6])
