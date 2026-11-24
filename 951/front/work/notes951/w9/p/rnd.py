# random two-world circuits on core systems with a 4-set; validates the PROVED lemmas and measures Pi* shortness.
from plib import *
import random, collections
CORES=[(8,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7]]),
       (9,[[0,1,2,3],[0,4,5],[1,4,6],[2,5,6],[3,4,7],[1,5,7],[0,6,8],[2,7,8],[3,5,8]])]
def rand_h(n,rng):
    k=rng.choice([1,2,2,3]); return [rng.sample(range(n),rng.choice([1,2,2,3])) for _ in range(k)]
def gen(n,sets,rng):
    b=B(n); mts=rand_h(n,rng)
    terms=[b.AND(M) for M in mts]; h=b.OR(terms)
    if h<n: return None
    N=b.g('not',h); outs=[]
    hfun=lambda x: any(all(x>>v&1 for v in M) for M in mts)
    for S in sets:
        S=list(S); rng.shuffle(S)
        mode=rng.choice(['honest','shannon','split','junk'])
        if mode=='honest': outs.append(b.OR(S)); continue
        # U0 part: A = N ∧ (chain), chain >= o_S on U0, <= o_S ∨ h
        ch=list(S)
        if mode=='junk': ch=ch+[rng.choice(terms)]
        rng.shuffle(ch); A=b.g('and',N,b.OR(ch))
        # U1 part: equal to o_S on U1, <= o_S everywhere
        if mode=='split':
            parts=[b.OR([b.g('and',u,t) for u in S]) for t in terms]
            Bp=b.OR(parts)
        else:
            Bp=b.g('and',h,b.OR([b.g('or',S[0],S[1])]+S[2:])) if rng.random()<.5 else b.OR([b.g('and',u,h) for u in S])
        outs.append(b.g('or',A,Bp))
    return b.out([sorted(S) for S in sets],outs)
if __name__=='__main__':
    rng=random.Random(1); st=collections.Counter(); keep=[]
    for it in range(1500):
        n,sets=CORES[it%2]; c=gen(n,sets,rng)
        if c is None or len(set(c['outs']))<len(sets): continue
        T=C(c)
        if not T.correct(): st['INCORRECT']+=1; continue
        st['circ']+=1; st['clean']+=T.clean(); st['ess']+=(not T.c0ok() and not T.c1ok())
        K=T.classes()
        for i in range(T.m):
            if T.hard[i]:
                st['hard']+=1
                k=sum(T.heavy[u] for u in T.sets[i])
                if len(K['D0'][i])<k-1: st['FAIL heavy lemma']+=1
                for M,sx in d0m(T,i).items():
                    if len(sx)<T.d[i]: st['FAIL (a\')']+=1
                if len(pistar(K,i))<T.d[i]: st['Pi* short (hard)']+=1
            else:
                st['easy']+=1
                if len(K['Dr'][i])<T.d[i]: st['FAIL thmE']+=1
                if not K['D1'][i]<=K['Dr'][i]: st['FAIL D1inDr']+=1
            for j in range(T.m):
                if j==i: continue
                hi,hj=T.hard[i],T.hard[j]
                proved=[('Dr','Dr'),('Dr','Pr'),('Pr','Pr'),('D1','D1'),('D1','Dr'),('D0','D0'),('D0','P0'),('P0','P0'),('D0','Pr'),('P0','Pr')]
                for a,bq in proved:
                    if K[a][i]&K[bq][j]: st['FAIL disj %s-%s'%(a,bq)]+=1
                if hj:
                    for a in ('D0','P0'):
                        if K[a][i]&K['Dr'][j]: st['FAIL disj %s-Dr(hard)'%a]+=1
                for a,bq in [('D1','Pr'),('D0','Dr'),('P0','Dr'),('D1','D0'),('D1','P0')]:
                    if K[a][i]&K[bq][j]: st['conflict %s-%s'%(a,bq)]+=1
        U=[pistar(K,i) for i in range(T.m)]
        if match(T.d,U)<T.base: st['Pi* matching fails']+=1
        U2=[pi2(T,K,i) for i in range(T.m)]
        if match(T.d,U2)<T.base: st['Pi** matching fails']+=1; keep.append(c)
    for k,v in sorted(st.items()): print(v,k)
    json.dump(keep[:5],open('rnd_fail.json','w'))
