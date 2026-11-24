# adversarial constructions for claim (iii): h = x_0 OR x_1
import sys, random, collections, json, itertools
from rl import *
from t5 import check5
class Bld:
    def __init__(s,n): s.n=n; s.g=[]; s.memo={}
    def G(s,op,i,j):
        if i==j: return i
        k=(op,min(i,j),max(i,j))
        if k not in s.memo: s.g.append([op,i,j]); s.memo[k]=s.n+len(s.g)-1
        return s.memo[k]
    def NOT(s,i): s.g.append(['not',i]); return s.n+len(s.g)-1
    def chain(s,op,ws,rng):
        ws=list(ws); rng.shuffle(ws)
        while len(ws)>1:
            if rng.random()<.5: i,j=0,1
            else: i,j=rng.sample(range(len(ws)),2)
            a,b=ws[i],ws[j]; ws=[w for t,w in enumerate(ws) if t not in (i,j)]+[s.G(op,a,b)]
        return ws[0]
def system(rng):
    r=rng.randint(1,3); c=rng.randint(1,3)
    pts=2; grid={}
    for i in range(r):
        for j in range(c):
            if rng.random()<.85: grid[i,j]=pts; pts+=1
    sets=[]
    for i in range(r):
        S=[0]+[grid[i,j] for j in range(c) if (i,j) in grid]
        if rng.random()<.4: S.append(pts); pts+=1
        sets.append(S)
    for j in range(c):
        S=[1]+[grid[i,j] for i in range(r) if (i,j) in grid]
        if rng.random()<.4: S.append(pts); pts+=1
        sets.append(S)
    n=pts+rng.randint(0,1)
    for _ in range(rng.randint(0,3)):
        S=sorted(rng.sample(range(2,n),min(n-2,rng.randint(2,3))))
        if len(S)>=2 and all(len(set(S)&set(T))<=1 for T in sets): sets.append(S)
    if rng.random()<.25 and n<10:
        S=[0,1,n]; n+=1; sets.append(S)
    sets=[S for S in sets if len(S)>=2]
    return n,sets
def build(rng):
    n,sets=system(rng)
    if n>9 or not sets: return None
    B=Bld(n); h=B.G('or',0,1); y=B.NOT(h)
    gp=lambda p: B.G('or',h,p)
    outs=[]
    for S in sets:
        rest=[u for u in S if u>1]
        mode=rng.choice(['honest','mux','mux','muxh','sel','sel','mux'])
        if mode=='honest': outs.append(B.chain('or',S,rng)); continue
        ws=[gp(p) if rng.random()<.75 else p for p in rest]
        if mode in ('mux','muxh'):
            if (0 in S or 1 in S) and all(w<n for w in ws): ws.append(h if rng.random()<.5 or not rest else gp(rest[0]))
            if not ws: ws=[h]
            Wd=B.chain('or',ws,rng)
            T=B.chain('or',S,rng)
            if mode=='muxh': T=B.G('and',h,T)
            outs.append(B.G('and',Wd,B.G('or',y,T)))
        else:
            if not ws: outs.append(B.chain('or',S,rng)); continue
            if rng.random()<.3: ws.append(h)
            Wd=B.chain('or',ws,rng)
            T=B.G('and',h,B.chain('or',S,rng)) if rng.random()<.6 else B.chain('or',[B.G('and',h,u) if u>1 else u for u in S],rng)
            if set(S)&{0,1} and rng.random()<.5:
                # x_a itself plus h AND rest
                T=B.chain('or',[u for u in S if u<2]+([B.G('and',h,B.chain('or',rest,rng))] if rest else []),rng)
            outs.append(B.G('or',B.G('and',Wd,y),T))
    return dict(n=n,sets=sets,gates=B.g,outs=outs)
def compact(c):
    n=c['n']; G=c['gates']; keep=set(); st=list(c['outs'])
    while st:
        w=st.pop()
        if w<n or w in keep: continue
        keep.add(w); st+=G[w-n][1:]
    order=sorted(keep); mp={w:n+i for i,w in enumerate(order)}
    f=lambda w: w if w<n else mp[w]
    return dict(n=n,sets=c['sets'],gates=[[G[w-n][0]]+[f(x) for x in G[w-n][1:]] for w in order],outs=[f(o) for o in c['outs']])
def valid(c):
    c=compact(c); Lc=L(c)
    if not Lc.ok or not Lc.correct or Lc.hx!=(Lc.xv[0]|Lc.xv[1]): return None
    return c,Lc
def mutate(c,rng):
    n=c['n']; G=[list(g) for g in c['gates']]; outs=list(c['outs']); k=rng.randrange(len(G)); r=rng.random()
    if G[k][0]=='not': 
        if r<.5 or n+k==0: return None
        # leave NOT alone mostly
        return None
    if r<.35:
        j=rng.randrange(1,3); G[k][j]=rng.randrange(n+k)
    elif r<.45: G[k][0]='and' if G[k][0]=='or' else 'or'
    elif r<.8:
        rep=G[k][rng.randrange(1,3)]; w=n+k
        G=[[g[0]]+[rep if x==w else x for x in g[1:]] for g in G]; outs=[rep if o==w else o for o in outs]
    else:
        # insert a new gate before position k reading two earlier wires and rewire one input of gate k to it
        new=[rng.choice(['and','or']),rng.randrange(n+k),rng.randrange(n+k)]
        sh=lambda x: x+1 if x>=n+k else x
        G=[[g[0]]+[sh(x) for x in g[1:]] for g in G]; outs=[sh(o) for o in outs]
        G.insert(k,new); G[k+1][rng.randrange(1,3)]=n+k
    return dict(n=n,sets=c['sets'],gates=G,outs=outs)
MODE='b'
def score(r): return (r['slack']+r['K']//2, r['marg']) if MODE=='b' else (r['marg'],-r['K'],r['slack']) if MODE=='m' else (not r['ess'], r['K']<2, 2*r['outside']-r['K'], r['slack'])   # distance to the claimed bound, then H2 margin
if __name__=='__main__':
    MODE=sys.argv[4] if len(sys.argv)>4 else 'b'; seed=int(sys.argv[1]); T=int(sys.argv[2]); steps=int(sys.argv[3]); rng=random.Random(seed)
    st=collections.Counter(); best=None; hist=collections.Counter(); minmarg=99; mm=None; tight=None; tk=None
    done=0
    while done<T:
        c=build(rng)
        if not c: continue
        v=valid(c)
        if not v:
            assert not L(compact(c)).ok, 'constructed circuit incorrect'; continue
        c,Lc=v; r=check5(Lc,0,1,rng,nmaps=2); done+=1; st['built']+=1; st['built_ess']+=r['ess']; st['built_K>0']+=r['K']>0
        cur=r
        for _ in range(steps):
            c2=mutate(c,rng)
            if not c2: continue
            v=valid(c2)
            if not v: continue
            c2,L2=v
            r2=check5(L2,0,1,rng,nmaps=2); st['mut_checked']+=1; st['mut_ess']+=r2['ess']
            hist[(r2['K'],min(r2['marg'],3))]+=1
            if r2['K']>=2 and r2['ess'] and (tk is None or 2*r2['outside']-r2['K']<2*tk[0]['outside']-tk[0]['K']): tk=(r2,c2)
            if r2['marg']<minmarg or (r2['marg']==minmarg and r2['K']>mm[0]['K']): minmarg=r2['marg']; mm=(r2,c2)
            d=r2['slack']+r2['K']//2
            if tight is None or d<tight[0]['slack']+tight[0]['K']//2 or (d==tight[0]['slack']+tight[0]['K']//2 and r2['K']>tight[0]['K']): tight=(r2,c2)
            if score(r2)<=score(cur) or rng.random()<.02: c,cur=c2,r2
        st['maxK']=max(st['maxK'],cur['K'])
    print(dict(st)); print('min(outside-K):',minmarg,mm[0]); print('tightest vs bound (s-1)-(base-K//2):',tight[0]['slack']+tight[0]['K']//2,tight[0])
    print('essential K>=2 minimising 2*outside-K:',tk)
    print('hist (K,marg<=3):',sorted(hist.items()))
    json.dump(dict(minmarg=mm,tight=tight),open('adv5_%d%s.json'%(seed,MODE),'w'))
