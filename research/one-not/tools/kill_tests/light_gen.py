# Random correct one-NOT circuits with junk, to stress the Lean gain statement (MUInduct.lean, D = ∅):
#   for every Q with base(Q) > 0 there is v ∉ Q with  Σ_{alive w ∋ v} (|S_w| - 1) ≤ |UC(∅,Q) \ UC(∅,Q+v)|.
# Construction: a random pool of AND/OR gates with exactly one NOT (of a monotone pool wire h); each output o_w is an
# OR tree over {x_u : u ∈ S_w} plus random existing wires whose real table is ≤ OR(S_w) (so the circuit is correct).
# Run: python3 -I research/one-not/tools/kill_tests/light_gen.py one-not SEED COUNT
import sys, os, random, collections
SEED=int(sys.argv[2]) if len(sys.argv)>2 else 0; COUNT=int(sys.argv[3]) if len(sys.argv)>3 else 300
sys.argv=[sys.argv[0],sys.argv[1] if len(sys.argv)>1 else 'research/one-not','0']
_here=os.path.dirname(os.path.abspath(__file__))
_src=open(os.path.join(_here,'mu_light.py')).read(); exec(_src[:_src.index("random.seed(1); CS=[]")])
SYS=[(5,[[0,1,2],[1,3],[2,4]]),(5,[[0,1,2],[2,3],[3,4]]),(4,[[0,1],[1,2],[2,3],[0,3]]),(4,[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]]),
     (6,[[0,1,2],[2,3,4],[4,5,0]]),(6,[[0,1,2],[0,3,4],[1,3,5]]),(6,[[0,1,2],[3,4,5],[0,3]]),(5,[[0,1,2,3],[0,4],[1,4]]),
     (7,[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]]),(6,[[0,1,2],[0,3,4],[1,3],[2,4,5]])]
def gen(rng):
    n,S=rng.choice(SYS); P=1<<n; FULL=(1<<P)-1
    G=[]; T=tables(n,[],'real')
    def add(g):
        G.append(g); T.append(tables(n,G,'real')[-1])
    k1=rng.randint(2,10); notpos=rng.randint(1,k1)
    for k in range(k1):
        if k==notpos-1 or (k==k1-1 and not any(g[0]=='not' for g in G)):
            mono=[i for i in range(len(T)) if i<n or (G[i-n][0]!='not' and not any(G[j][0]=='not' for j in range(i-n)))]
            hi=rng.choice([i for i in mono if i>=n] or mono); add(['not',hi]); continue
        a,b=rng.sample(range(len(T)),2); add([rng.choice(['and','and','or']),a,b])
    outs=[None]*len(S)
    for w in rng.sample(range(len(S)),len(S)):
        R=S[w]; ow=0
        for u in R: ow|=T[u]
        cand=[i for i in range(n,len(T)) if T[i] and T[i]&~ow==0]
        items=list(R)+rng.sample(cand,min(len(cand),rng.randint(0,5)))
        rng.shuffle(items)
        while len(items)>1:
            a=items.pop(); b=items.pop(); add(['or',a,b]); items.insert(rng.randint(0,len(items)),n+len(G)-1)
            # occasionally reuse another existing wire ≤ o_w
            if rng.random()<0.2:
                cand=[i for i in range(n,len(T)) if T[i] and T[i]&~ow==0 and i not in items]
                if cand: items.append(rng.choice(cand))
        outs[w]=items[0]
    return n,S,G,outs
RULES={}
rng=random.Random(SEED); st=collections.Counter(); fails=[]
for it in range(COUNT):
    n,S,G,outs=gen(rng)
    if sum(g[0]=='not' for g in G)!=1: continue
    c=mk('gen%d_%d'%(SEED,it),n,S,G,outs)
    if c is None: st['incorrect?']+=1; continue
    st['circuits']+=1
    for Q in range(1<<n):
        b=base(c,0,Q)
        if b==0: continue
        cb=cube(c,0,Q); hh=c['h']&cb; P=apts(c,0,Q)
        kind='h const' if hh in (0,cb) else ('heavy' if any((c['h']>>(Q|1<<v))&1 for v in P) else 'light')
        if any(not (Q>>x&1) and x not in P for x in range(n)): st[kind+': free point (trivial)']+=1; continue
        U=UC(c,0,Q); gn={v:len(U-UC(c,0,Q|1<<v)) for v in P}; cs={v:b-base(c,0,Q|1<<v) for v in P}; ok=[v for v in P if gn[v]>=cs[v]]
        st[kind+': uniform average gain >= cost']+=sum(gn.values())>=sum(cs.values())
        per=[sum(gn[v] for v in R)>=sum(cs[v] for v in R) for R in alive(c,0,Q)]
        st[kind+': A_w (average over S_w) for every alive w']+=all(per)
        if kind=='light' and not all(per): fails.append(('A_w',c['name'],Q,S,G,outs))
        for nm,rule in RULES.items(): st[kind+': rule '+nm]+=gn[rule(c,Q,P)]>=cs[rule(c,Q,P)]
        st[kind+': instances']+=1; st[kind+': some v good']+=bool(ok); st[kind+': every v good']+=len(ok)==len(P)
        if not ok: fails.append((kind,c['name'],Q,S,G,outs))
for k,v in sorted(st.items()): print('%-40s %d'%(k,v))
for f in fails[:5]: print('FAIL',f)
