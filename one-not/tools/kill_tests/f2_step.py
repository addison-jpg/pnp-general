# F2 STEP harness (opus-f2-step lane). D = empty.
# F2(Q) = OR gates g with a REAL witness (alive w, Z ⊇ Q, Z ∩ S_w = ∅, u ≠ u' ∈ S_w, g(Z)=0, g(Z+u)=g(Z+u')=1).
# Usage as library: exec this file's top part; or run: python3 -I f2_step.py one-not [SEED COUNT]
import sys, os, itertools, collections, functools, random, json, glob
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'
_ARGS=sys.argv[2:]
sys.argv=['x',ROOT,'9']
_here=os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() and __file__.endswith('f2_step.py') else os.path.join(ROOT,'tools','kill_tests')
_src=open(os.path.join(_here,'canon.py')).read(); exec(_src[:_src.index("st=collections.Counter()")])
def mk(name,n,S,G,outs):
    Wr=tables(n,G,'real'); P_=1<<n; FULL=(1<<P_)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): return None
    nots=[g for g in G if g[0]=='not']
    if len(nots)!=1: return None
    h=Wr[nots[0][1]]; X=Wr[:n]; wm={}
    AV=[]
    for R in S:
        av=FULL
        for u in R: av&=FULL^X[u]
        AV.append(av)
    for k,g in enumerate(G):
        if g[0]!='or': continue
        i=n+k
        for wi,R in enumerate(S):
            M=0
            for a,b in itertools.combinations(R,2):
                M|=(FULL^Wr[i])&(Wr[i]>>(1<<a))&(Wr[i]>>(1<<b))&AV[wi]
            if M: wm[(i,wi)]=M
    return dict(name=name,n=n,S=S,G=G,outs=outs,W=Wr,h=h,X=X,FULL=FULL,wm=wm,AV=AV)
def cube(c,Q):
    m=c['FULL']
    for v in range(c['n']):
        if Q>>v&1: m&=c['X'][v]
    return m
def aliveW(c,Q): return [wi for wi,R in enumerate(c['S']) if not any(Q>>u&1 for u in R)]
def F2(c,Q):
    cb=cube(c,Q); al=set(aliveW(c,Q))
    return {i for (i,wi),M in c['wm'].items() if wi in al and M&cb}
def cost(c,Q,v): return sum(len(c['S'][w])-1 for w in aliveW(c,Q) if v in c['S'][w])
def apts(c,Q): return sorted({u for w in aliveW(c,Q) for u in c['S'][w]})
def ok(n,S,G,outs):
    return sum(1 for g in G if g[0]=='not')==1 and len(S)>=1 and not any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) and all(len(R)>=2 for R in S)
def corpus(NMAX=9):
    CS=[]
    for name,n,S,G,outs in circuits():
        if n>NMAX or not ok(n,S,G,outs): continue
        c=mk(name,n,S,G,outs)
        if c: CS.append(c)
    return CS
def randgen(seed,count):
    src=open(os.path.join(_here,'light_gen.py')).read()
    g={}; exec(src[src.index('SYS=['):src.index('RULES={}')],g)
    ns=dict(g); ns['tables']=tables
    rng=random.Random(seed); out=[]
    gen=g['gen']; gen.__globals__['tables']=tables
    for it in range(count):
        n,S,G,outs=gen(rng)
        if sum(x[0]=='not' for x in G)!=1: continue
        c=mk('gen%d_%d'%(seed,it),n,S,G,outs)
        if c: out.append(c)
    return out
