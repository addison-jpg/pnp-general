# product design D(r,2,mu) (r prime): world-0 circuit {g_w >= A_w, exact on weight<=1}; count gates, verify
import itertools, random, json, sys
r=int(sys.argv[1]); mu=int(sys.argv[2])
P2=[(x,y) for x in range(r) for y in range(r)]
def lines(c):  # slope class c: 0..r-1 slopes, r = vertical
    if c==r: return [frozenset((b,y) for y in range(r)) for b in range(r)]
    return [frozenset((x,(c*x+b)%r) for x in range(r)) for b in range(r)]
pts=[(a,b) for a in P2 for b in P2]; idx={p:i for i,p in enumerate(pts)}; n=len(pts)
gates=[]
def G(t,a,b): gates.append([t,a,b]); return n+len(gates)-1
def chain(t,ws):
    w=ws[0]
    for v in ws[1:]: w=G(t,w,v)
    return w
colA={a:chain('or',[idx[(a,b)] for b in P2]) for a in P2}   # OR over {a} x B
colB={b:chain('or',[idx[(a,b)] for a in P2]) for b in P2}
sets=[];outs=[]
for c in range(mu):
    LA={l:chain('or',[colA[a] for a in sorted(l)]) for l in lines(c)}
    LB={l:chain('or',[colB[b] for b in sorted(l)]) for l in lines(c)}
    for l1 in lines(c):
        for l2 in lines(c):
            sets.append(sorted(idx[(a,b)] for a in l1 for b in l2)); outs.append(G('and',LA[l1],LB[l2]))
base=sum(len(S)-1 for S in sets)
for i in range(len(sets)):
    for j in range(i): assert len(set(sets[i])&set(sets[j]))<=1
def ev(x):
    w=list(x)
    for t,a,b in gates: w.append(w[a]&w[b] if t=='and' else w[a]|w[b])
    return w
ok=True
for u in range(-1,n):
    x=[0]*n
    if u>=0: x[u]=1
    w=ev(x); ok&=all(w[o]==int(u in S) for o,S in zip(outs,sets))
ge=True; strict=0
for _ in range(300):
    k=random.choice([2,3,5,10,30]); x=[0]*n
    for u in random.sample(range(n),k): x[u]=1
    w=ev(x)
    for o,S in zip(outs,sets):
        a=int(any(x[u] for u in S)); ge&=w[o]>=a; strict+=w[o]>a
print('D(%d,2,%d): n=%d lines=%d size=%d base=%d  world-0 gates=%d  exact on weight<=1: %s  >=A on random: %s (strictly above %d times)'%(r,mu,n,len(sets),len(sets[0]),base,len(gates),ok,ge,strict))
json.dump(dict(n=n,sets=sets,gates=gates,outs=outs),open('prod_%d_%d_world0.json'%(r,mu),'w'))
