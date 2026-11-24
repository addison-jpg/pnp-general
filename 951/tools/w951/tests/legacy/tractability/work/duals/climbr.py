# Adversarial climb against the X-rule and FracMatch: mutate clean correct essential one-NOT circuits.
# python3 climbx.py seed.json STEPS RNGSEED MAXSIZE out.jsonl
import sys,json,random,time,os
import resid as RS, xrule as XR, relrule as RR
from verify import verify
args=sys.argv[1:]; c0=json.load(open(args[0])); STEPS=int(args[1]); rng=random.Random(int(args[2])); MAXS=int(args[3]); out=open(args[4],'a',buffering=1)
def tt_ok(c):
    n,G,S,O=c['n'],c['gates'],c['sets'],c['outs']; R=1<<n; full=(1<<R)-1
    X=[sum(1<<r for r in range(R) if r>>i&1) for i in range(n)]
    def ev(cv=None):
        w=list(X)
        for g in G:
            if g[0]=='not': w.append(full^w[g[1]] if cv is None else (full if cv else 0))
            elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
            else: w.append(w[g[1]]|w[g[2]])
        return w
    w=ev(); want=[0]*len(S)
    for i,s in enumerate(S):
        for v in s: want[i]|=X[v]
    if any(w[o]!=want[i] for i,o in enumerate(O)): return False
    if len(set(w))<len(w) or any(t in (0,full) for t in w): return False      # clean
    for cv in (0,1):
        u=ev(cv)
        if all(u[o]==want[i] for i,o in enumerate(O)): return False           # essential
    read=set(O)|{j for g in G for j in g[1:]}
    return all(n+k in read for k in range(len(G)))
def mutate(c):
    n,G,O=c['n'],[list(g) for g in c['gates']],list(c['outs']); s=len(G); r=rng.random()
    if r<0.5 and s<MAXS:
        k=rng.randint(0,s); W=n+k; a,b=rng.randrange(W),rng.randrange(W)
        if a==b: return None
        newg=[rng.choice(['and','or']),a,b]; G2=[]
        for i,g in enumerate(G):
            if i==k: G2.append(newg)
            G2.append([g[0]]+[x+1 if x>=W else x for x in g[1:]])
        if k==s: G2.append(newg)
        O2=[o+1 if o>=W else o for o in O]
        readers=[(i,j) for i in range(k+1,len(G2)) for j in range(1,len(G2[i]))]
        if not readers: return None
        i,j=rng.choice(readers); G2[i][j]=W
        return {'n':n,'sets':c['sets'],'gates':G2,'outs':O2}
    i=rng.randrange(s); j=rng.randint(1,len(G[i])-1); G[i][j]=rng.randrange(n+i)
    if G[i][0]!='not' and rng.random()<0.3: G[i][0]='and' if G[i][0]=='or' else 'or'
    if G[i][0]!='not' and G[i][1]==G[i][2]: return None
    return {'n':n,'sets':c['sets'],'gates':G,'outs':O}
def score(c):
    Lr=RR.run(c,WT=1,verbose=False)[0]; return (round(Lr,6),)
def score_old(c):
    F=RS.full(c); o=XR.xrule(c,F); dem=[len(s)-1 for s in c['sets']]
    deficit=sum(max(0,r['d']-r['x']) for r in o); spare=sum(min(r['x']-r['d'],3) for r in o if len(c['sets'][r['w']])>=4)
    L,pi,mu,_=RS.lpdual([[C for C,z,hz in m] for m in F],dem)
    return (deficit,-spare,round(L,6))
assert tt_ok(c0),'seed not clean/correct/essential'
cur=c0; sc=score(cur); t0=time.time(); seen=0
print('seed',args[0],'score',sc,flush=True)
for step in range(STEPS):
    m=mutate(cur)
    if m is None or not tt_ok(m): continue
    s2=score(m)
    seen+=1
    if s2[0]>1+1e-7:
        out.write(json.dumps({'score':s2,'c':m})+'\n')
    if s2>=sc:
        if s2>sc: print(step,'score',s2,'size',len(m['gates']),'%.0fs'%(time.time()-t0),flush=True)
        if s2>sc: out.write(json.dumps({'improve':s2,'c':m})+'\n')
        cur,sc=m,s2
out.write(json.dumps({'final':sc,'c':cur})+'\n'); print('done',sc,'valid mutants',seen,'%.0fs'%(time.time()-t0),flush=True)
