# Adversarial local search for a failure of the F2 STEP (fable-f2-step lane).
# Genome: a correct one-NOT circuit; move: redirect one gate input / flip and-or / insert a gate, keeping correctness.
# Fitness (maximised): max over Q of min over alive v of (cost(v) - gain(v));  >= 1 means STEP FAILS at that Q.
# Run: python3 -I research/one-not/tools/kill_tests/f2_adv.py SEED ITERS [mono]     (mono: keep the NOT gate unread)
import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from f2lib import *
SEED=int(sys.argv[1]); ITERS=int(sys.argv[2]); MONO=len(sys.argv)>3 and sys.argv[3]=='mono'
rng=random.Random(SEED)
def fit(c):
    best=(-99,0.0); arg=None
    for Q in range(1<<c['n']):
        if not aliveW(c,Q): continue
        F,r=stepinfo(c,Q)
        m=min(k-g for g,k in r.values()); fr=sum(1 for g,k in r.values() if g<k)/len(r)
        if (m,fr)>best: best=(m,fr); arg=Q
    return best,arg
def valid(n,S,G,outs):
    ni=[k for k,g in enumerate(G) if g[0]=='not']
    if len(ni)!=1: return None
    k=ni[0]
    # the NOT input must be monotone: it must not depend on the NOT (it precedes it) - automatic
    if MONO and any(n+k in g[1:] for g in G): return None
    return mk('adv',n,S,G,outs)
def mutate(n,S,G,outs):
    G=[list(g) for g in G]; outs=list(outs); r=rng.random()
    if r<0.6:
        k=rng.randrange(len(G)); g=G[k]
        if g[0]=='not': g[1]=rng.randrange(n+k)
        else: g[rng.randint(1,2)]=rng.randrange(n+k)
    elif r<0.75:
        k=rng.randrange(len(G))
        if G[k][0]!='not': G[k][0]='and' if G[k][0]=='or' else 'or'
    elif r<0.9 and len(G)<40:
        # insert a gate at position k, shift references
        k=rng.randrange(len(G)+1); new=[rng.choice(['and','or']),rng.randrange(n+k),rng.randrange(n+k)]
        sh=lambda x: x+1 if x>=n+k else x
        G=[[g[0]]+[sh(x) for x in g[1:]] for g in G]; G.insert(k,new); outs=[sh(o) for o in outs]
        # splice: redirect one later input to the new gate
        later=[j for j in range(k+1,len(G)) if G[j][0]!='not']
        if later: j=rng.choice(later); G[j][rng.randint(1,2)]=n+k
    else:
        w=rng.randrange(len(outs)); outs[w]=rng.randrange(n,n+len(G))
    return G,outs
best_all=(-99,0)
for start in range(10**9):
    cs=randgen(rng.randrange(10**9),30)
    cs=[c for c in cs if valid(c['n'],c['S'],c['G'],c['outs'])]
    if not cs: continue
    c=rng.choice(cs); f,arg=fit(c)
    for it in range(ITERS):
        G,outs=mutate(c['n'],c['S'],c['G'],c['outs'])
        c2=valid(c['n'],c['S'],G,outs)
        if c2 is None: continue
        f2,arg2=fit(c2)
        if f2>=f: c,f,arg=c2,f2,arg2
        if f[0]>=1:
            print('STEP FAILS',json.dumps(dict(n=c['n'],sets=c['S'],gates=c['G'],outs=c['outs'],Q=arg))); sys.stdout.flush(); break
    if f>best_all: best_all=f; print('start',start,'best',f,'Q',arg,json.dumps(dict(n=c['n'],sets=c['S'],gates=c['G'],outs=c['outs']))); sys.stdout.flush()
