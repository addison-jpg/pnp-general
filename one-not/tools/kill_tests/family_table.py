# Candidate families F(Q) for the STEP/MU proof effort. D = empty. Writes a markdown table to stdout.
# Run: python3 -I one-not/tools/kill_tests/family_table.py one-not > /tmp/out.md   (about a minute)
# Family elements: OR gates g with a witness (alive w at Q, Z ⊇ Q, Z∩S_w=∅, atoms u≠u' in S_w):
#  F1 UC: face1 h(Z)=0,C1g(Z)=0,C1g(Z+u)=C1g(Z+u')=1  or face0 C0g(Z)=0,h(Z+u)=h(Z+u')=1,C0g(Z+u)=C0g(Z+u')=1
#  F2 real: g(Z)=0, g(Z+u)=g(Z+u')=1     F3 UC with face1 atoms each needing real g(Z+a)=1 or h(Z+a)=0
#  F4 = F1, F5 = F2 with the witness set w required to have g in the syntactic cone of outs[w]. F6 skipped (unspecified).
import sys, os, itertools, glob, json, functools
ROOT=sys.argv[1] if len(sys.argv)>1 else 'one-not'
sys.argv=['x',ROOT,'9']
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'canon.py')).read(); exec(src[:src.index("st=collections.Counter()")])
FAMS=['F1','F2','F3','F4','F5']
def build(name,n,S,G,outs):
    Wr=tables(n,G,'real'); W0=tables(n,G,0); W1=tables(n,G,1); P_=1<<n; FULL=(1<<P_)-1
    if any(Wr[o]!=functools.reduce(lambda a,b:a|b,[Wr[u] for u in R],0) for o,R in zip(outs,S)): return None
    h=Wr[[g for g in G if g[0]=='not'][0][1]]; X=Wr[:n]
    cone=[]
    for o in outs:
        seen=set(); st=[o]
        while st:
            x=st.pop()
            if x in seen or x<n: continue
            seen.add(x); st+=G[x-n][1:]
        cone.append(seen)
    pw={f:{} for f in FAMS}
    for k,g in enumerate(G):
        if g[0]!='or': continue
        i=n+k
        for wi,R in enumerate(S):
            av=FULL
            for u in R: av&=FULL^X[u]
            for a,b in itertools.combinations(R,2):
                sa=1<<a; sb=1<<b
                f1=(FULL^W1[i])&(W1[i]>>sa)&(W1[i]>>sb)&av&(FULL^h)
                f0=(FULL^W0[i])&(W0[i]>>sa)&(W0[i]>>sb)&av&(h>>sa)&(h>>sb)
                ca=(Wr[i]>>sa)|(FULL^(h>>sa)); cb_=(Wr[i]>>sb)|(FULL^(h>>sb))
                m={'F1':f1|f0,'F3':(f1&ca&cb_)|f0,'F2':(FULL^Wr[i])&(Wr[i]>>sa)&(Wr[i]>>sb)&av}
                m['F4']=m['F1'] if i in cone[wi] else 0; m['F5']=m['F2'] if i in cone[wi] else 0
                for f in FAMS:
                    if m[f]: pw[f].setdefault(i,[]).append((wi,m[f]))
    return dict(name=name,n=n,S=S,ng=len(G),FULL=FULL,X=X,pw=pw)
def cube(c,Q):
    m=c['FULL']
    for v in range(c['n']):
        if Q>>v&1: m&=c['X'][v]
    return m
def run(c):
    n=c['n']; S=c['S']; res=[]
    cubes=[cube(c,Q) for Q in range(1<<n)]
    F={f:[frozenset(g for g,L in c['pw'][f].items() if any(not any(Q>>u&1 for u in S[w]) and M&cubes[Q] for w,M in L)) for Q in range(1<<n)] for f in FAMS}
    for Q in range(1<<n):
        al=[R for R in S if not any(Q>>u&1 for u in R)]
        if not al: continue
        base=sum(len(R)-1 for R in al); pts=sorted({u for R in al for u in R})
        cost={v:sum(len(R)-1 for R in al if v in R) for v in pts}
        for f in FAMS:
            mu=len(F[f][Q]); best=max((len(F[f][Q]-F[f][Q|1<<v])-cost[v],v) for v in pts)
            res.append((f,c['name'],n,c['ng'],Q,mu,base,best[0]))   # best[0]>=0 iff STEP holds
    return res
def load(files):
    out=[]
    for f in files:
        d=json.load(open(f)); G=[[g[0]]+[int(x) for x in g[1:]] for g in d['gates']]
        out.append((os.path.basename(f),d['n'],[list(s) for s in d['sets']],G,list(d['outs'])))
    return out
def ok(n,S,G,outs):
    return sum(1 for g in G if g[0]=='not')==1 and len(S)>=2 and not any(len(set(a)&set(b))>1 for a,b in itertools.combinations(S,2)) and all(len(R)>=2 for R in S)
wit=sorted(glob.glob(ROOT+'/data/witnesses/*.json')); witkeys={json.dumps([d[1],d[2],d[3],d[4]]) for d in load(wit)}
corp=[t for t in circuits() if t[1]<=8 and not t[0].startswith('data/witnesses/') and ok(*t[1:]) and json.dumps([t[1],t[2],t[3],t[4]]) not in witkeys]
def go(items):
    R=[]
    for t in items:
        if not ok(*t[1:]): continue
        c=build(t[0].split('/')[-1],*t[1:])
        if c: R+=run(c)
    return R
def summ(title,R):
    print('\n### %s'%title); print('| family | instances | MU ok | STEP ok | MU fails | STEP fails |'); print('|---|---|---|---|---|---|')
    for f in FAMS:
        r=[x for x in R if x[0]==f]; mf=[x for x in r if x[5]<x[6]]; sf=[x for x in r if x[7]<0]
        print('| %s | %d | %d | %d | %d | %d |'%(f,len(r),len(r)-len(mf),len(r)-len(sf),len(mf),len(sf)))
    for f in FAMS:
        r=[x for x in R if x[0]==f]
        for lab,fl,key in (('MU',[x for x in r if x[5]<x[6]],lambda x:(x[2],x[3],bin(x[4]).count('1'))),('STEP',[x for x in r if x[7]<0],lambda x:(x[2],x[3],bin(x[4]).count('1')))):
            fl.sort(key=key)
            if fl: print('- %s %s smallest: %s'%(f,lab,'; '.join('%s Q=%s |F|=%d base=%d bestgain-cost=%d'%(x[1],bin(x[4])[2:].zfill(x[2])[::-1],x[5],x[6],x[7]) for x in fl[:3])))
print('## Family table (D = empty)'); RC=go(corp); RW=go(load(wit))
print('corpus circuits: %d (n<=8, one NOT, correct)'%len({x[1] for x in RC}))
summ('(a) corpus',RC); summ('(b) barrier suite (data/witnesses/*.json)',RW)
print('\n### pappus_junk_gain.json at Q = empty'); print('| family | |F| | base | best gain-cost | MU | STEP |'); print('|---|---|---|---|---|---|')
for f in FAMS:
    x=[x for x in RW if x[0]==f and x[1]=='pappus_junk_gain.json' and x[4]==0][0]
    print('| %s | %d | %d | %d | %s | %s |'%(f,x[5],x[6],x[7],x[5]>=x[6],x[7]>=0))
print('\n### Families keeping MU on every instance (corpus + suite) AND STEP on pappus at Q=empty')
for f in FAMS:
    allmu=all(x[5]>=x[6] for x in RC+RW if x[0]==f); p=[x for x in RW if x[0]==f and x[1]=='pappus_junk_gain.json' and x[4]==0][0]
    print('- %s: MU everywhere=%s, pappus STEP=%s -> %s'%(f,allmu,p[7]>=0,'PASS' if allmu and p[7]>=0 else 'fail'))
