# F2 STEP library (fable-f2-step lane). Import after sys.path.insert(0, <this dir>); ROOT via env F2ROOT (default '951').
# c = mk(name,n,S,G,outs): dict with real tables W, C_0 tables W0, C_1 tables W1, h, X (input tables), wm (witness masks).
import sys, os, itertools, collections, functools, random, json
_here=os.path.dirname(os.path.abspath(__file__))
ROOT=os.environ.get('F2ROOT','951')
_sv=sys.argv; sys.argv=['x',ROOT,'9']
_src=open(os.path.join(_here,'canon.py')).read(); exec(_src[:_src.index("st=collections.Counter()")])
sys.argv=_sv
JUNK2=('JUNK2',6,[[0,1,2],[2,3],[4,5]],[['and',0,3],['and',4,5],['not',7],['or',2,6],['or',1,9],['or',10,0],['or',2,3],['or',4,5]],[11,12,13])
def bit(t,x): return (t>>x)&1
def mk(name,n,S,G,outs,need_not=True):
    Wr=tables(n,G,'real'); P_=1<<n; FULL=(1<<P_)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): return None
    nots=[g for g in G if g[0]=='not']
    if len(nots)>1 or (need_not and len(nots)!=1): return None
    h=Wr[nots[0][1]] if nots else 0
    X=Wr[:n]; wm={}; AV=[]
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
    return dict(name=name,n=n,S=S,G=G,outs=outs,W=Wr,W0=tables(n,G,0),W1=tables(n,G,1),h=h,X=X,FULL=FULL,wm=wm,AV=AV)
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
def stepinfo(c,Q):
    F=F2(c,Q); return F,{v:(len(F-F2(c,Q|1<<v)),cost(c,Q,v)) for v in apts(c,Q)}
def M(c,w,Z):
    R=c['S'][w]; return merges(c['W'],c['n'],c['G'],R,Z,{u:Z|1<<u for u in R})
def ok(n,S,G,outs):
    return sum(1 for g in G if g[0]=='not')==1 and len(S)>=1 and not any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) and all(len(R)>=2 for R in S)
def corpus(NMAX=9):
    CS=[]
    for name,n,S,G,outs in circuits():
        if n>NMAX or not ok(n,S,G,outs): continue
        c=mk(name,n,S,G,outs)
        if c: CS.append(c)
    c=mk(*JUNK2); CS.append(c)
    return CS
_gen=None
def randgen(seed,count):
    global _gen
    if _gen is None:
        src=open(os.path.join(_here,'light_gen.py')).read()
        g={}; exec(src[src.index('SYS=['):src.index('RULES={}')],g); g['tables']=tables; _gen=g['gen']
    rng=random.Random(seed); out=[]
    for it in range(count):
        n,S,G,outs=_gen(rng)
        if sum(x[0]=='not' for x in G)!=1: continue
        c=mk('gen%d_%d'%(seed,it),n,S,G,outs)
        if c: out.append(c)
    return out
def show(c):
    n=c['n']; print(c['name'],'n',n,'sets',c['S'],'outs',c['outs'])
    for k,g in enumerate(c['G']): print('  ',n+k,g)
