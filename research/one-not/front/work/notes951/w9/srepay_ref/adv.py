# adversarial constructed circuits: correct by truth table, essential NOT, hyperforest (and some cyclic) systems, many world-1 collisions
import random, json, itertools, collections, sys
from ref import check, UF
class Bld:
    def __init__(s,n): s.n=n; s.G=[]; s.memo={}; s.vs={}   # vs: wire -> frozenset of vars for pure OR wires
    def g(s,op,a,b=None):
        key=(op,a) if b is None else (op,min(a,b),max(a,b))
        if key in s.memo: return s.memo[key]
        s.G.append(['not',a] if b is None else [op,a,b]); w=s.n+len(s.G)-1; s.memo[key]=w; return w
    def ORset(s,T,rng,share=True):
        T=frozenset(T); assert T
        items={}  # wire -> varset
        rem=set(T)
        if share:
            cands=[(w,v) for w,v in s.vs.items() if v<=T and len(v)>=2]; rng.shuffle(cands)
            for w,v in cands:
                if rng.random()<0.7 and (v&rem):   # overlapping reuse allowed (idempotent OR)
                    items[w]=v; rem-=v
        for u in rem: items[u]=frozenset([u])
        ws=list(items)
        while len(ws)>1:
            rng.shuffle(ws); a=ws.pop(); b=ws.pop(); w=s.g('or',a,b)
            v=items[a]|items[b]; items[w]=v; s.vs[w]=v; ws.append(w)
        return ws[0]
def forest_system(n,rng,cyclic=False):
    pts=list(range(n)); rng.shuffle(pts); used=[]; comp=UF(range(n)); sets=[]
    free=pts[:]
    while free:
        k=rng.choice([2,3,3,4,4,5]); new=[free.pop() for _ in range(min(len(free),rng.randint(1,k)))]
        S=list(new)
        # attach to existing components, at most one point each
        comps=collections.defaultdict(list)
        for u in used: comps[comp.f(u)].append(u)
        cl=list(comps.values()); rng.shuffle(cl)
        for cc in cl[:rng.choice([0,1,1,2])]:
            if len(S)<k+1: S.append(rng.choice(cc))
        if len(S)<2:
            if used: S.append(rng.choice(used))
            else: free.extend(new); continue
        if not all(len(set(S)&set(T))<=1 for T in sets): continue
        for u in S[1:]: comp.u(S[0],u)
        used.extend(new); sets.append(sorted(S))
    if cyclic:
        for _ in range(rng.randint(1,3)):
            S=rng.sample(range(n),rng.choice([2,3]))
            if all(len(set(S)&set(T))<=1 for T in sets): sets.append(sorted(S))
    return sets
def build(n,sets,rng,hmode):
    b=Bld(n)
    # h
    if hmode=='th2' or hmode=='th2heavy':
        order=list(range(n)); rng.shuffle(order)
        o=order[0]; t=None
        for v in order[1:]:
            a=b.g('and',o,v); t=a if t is None else b.g('or',t,a); o=b.g('or',o,v); b.vs[o]=frozenset(order[:order.index(v)+1])
        h=t
        if hmode=='th2heavy': h=b.g('or',h,rng.randrange(n))
        ok=lambda a,c: True
    if rng.random()<0.5:
        # some junk mixed ORs early (cross merges / collisions seeds)
        for _ in range(rng.randint(0,4)):
            T=rng.sample(range(n),rng.randint(2,min(n,5))); b.ORset(T,rng)
    N=b.g('not',h)
    outs=[]; kinds=[]
    for wi,S in enumerate(sets):
        rest=[v for v in range(n) if v not in S]; rng.shuffle(rest)
        kind='A' if wi==0 else rng.choice('AABM')
        k1=rng.randint(1,max(1,len(rest)//2)) if rest else 0; T1=rest[:k1]; T2=rest[k1:k1+rng.randint(1,max(1,len(rest)-k1))] if len(rest)>k1 else []
        if kind=='M' or not T1 or not T2:
            outs.append(b.ORset(S,rng)); kinds.append('M'); continue
        P=b.ORset(set(S)|set(T1),rng); K=b.ORset(set(S)|set(T2),rng); R=b.ORset(S,rng)
        if kind=='A':
            x=rng.choice([lambda: b.g('and',b.g('and',P,K),N), lambda: b.g('and',b.g('and',P,N),K), lambda: b.g('and',b.g('and',P,N),b.g('and',K,N))])()
            outs.append(b.g('or',x,b.g('and',R,h)))
        else:
            # B: (R ∨ (N∧P)) ∧ (K ∨ h)
            outs.append(b.g('and',b.g('or',R,b.g('and',N,P)),b.g('or',K,h)))
        kinds.append(kind)
    if len(set(outs))<len(outs): return None
    return dict(n=n,sets=sets,gates=b.G,outs=outs,kinds=kinds)
def shuffle_topo(c,rng):
    n=c['n']; G=c['gates']; m=len(G); done=set(range(n)); order=[]; rem=set(range(m))
    while rem:
        ready=[k for k in rem if all(x in done for x in G[k][1:])]
        k=rng.choice(ready); rem.discard(k); order.append(k); done.add(n+k)
    new={v:v for v in range(n)}
    for i,k in enumerate(order): new[n+k]=n+i
    G2=[[G[k][0]]+[new[x] for x in G[k][1:]] for k in order]
    return dict(n=n,sets=c['sets'],gates=G2,outs=[new[x] for x in c['outs']])
if __name__=='__main__':
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 3000
    st=collections.Counter(); best=None; saved=[]
    for it in range(NT):
        n=rng.randint(4,10); cyc=rng.random()<0.3
        sets=forest_system(n,rng,cyc)
        if len(sets)<2: continue
        c=build(n,sets,rng,rng.choice(['th2','th2','th2heavy']))
        if c is None: continue
        c=shuffle_topo(c,rng)
        r,v=check(c)
        if not r['correct']: st['incorrect(discarded)']+=1; continue
        if not r['ess']: st['iness']+=1
        else: st['ess']+=1
        if r.get('h0'): st['h0=1']+=1; continue
        st['checked']+=1
        f=r['cyc']==0
        st['forest' if f else 'cyclic']+=1
        if r['coll']>0: st['coll>0 '+('forest' if f else 'cyclic')+(' ess' if r['ess'] else '')]+=1
        st['maxcoll']=max(st['maxcoll'],r['coll']); st['max k_g']=max(st['max k_g'],r['kmax'])
        if f and r['ess']:
            st['forest ess min(X-coll)']=min(st.get('forest ess min(X-coll)',99),r['X']-r['coll'])
            st['forest ess min(s-1-base)']=min(st.get('forest ess min(s-1-base)',99),r['s']-1-r['base'])
            if r['struct2_bad']: st['forest ess: double merge with an INPUT child']+=1
            if r['coll']>=3 and len(saved)<3: saved.append(c)
        if r['struct_bad']: st['struct_bad']+=1
        if v: st['VIOL']+=1; print('VIOL',sorted(set(v)),r,json.dumps(c))
    print(dict(st))
    json.dump(saved,open('adv_saved_%s.json'%(sys.argv[1] if len(sys.argv)>1 else '1'),'w'))
