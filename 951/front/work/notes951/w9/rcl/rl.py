# referee library for coord-lateral (independent implementation)
import json, glob, itertools, random, collections
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
def files():
    fs=sorted(glob.glob(F+'w8/cx*.json'))+sorted(glob.glob(F+'w9/p/*.json'))+sorted(glob.glob(F+'w9/fc/*.json'))
    fs+=sorted(glob.glob(F+'w9/tw/*.json'))+sorted(glob.glob(F+'w9/g3/*.json'))+sorted(glob.glob(F+'w9/srepay_ref/*.json'))
    for f in fs:
        c=json.load(open(f))
        if isinstance(c,dict) and 'gates' in c: yield f.replace(F,''),c
    for f in sorted(glob.glob(F+'w7/*.jsonl'))+[F+'chk/c.jsonl']:
        for i,l in enumerate(open(f)):
            if l.strip():
                c=json.loads(l)
                if isinstance(c,dict) and 'gates' in c: yield f.replace(F,'')+':%d'%i,c
class L:
    """lifted circuit. wires 0..n-1 = x, n+k = gate k; the NOT gate's wire is the input y."""
    def __init__(s,c):
        s.n=n=c['n']; s.G=[list(g) for g in c['gates']]; s.S=[list(x) for x in c['sets']]; s.outs=list(c['outs'])
        s.N=N=1<<n; s.lo=lo=(1<<N)-1; s.full=(1<<(2*N))-1
        xv=[]
        for i in range(n):
            blk=((1<<(1<<i))-1)<<(1<<i); t=0; per=1<<(i+1)
            # replicate
            t=blk; w=per
            while w<N: t|=t<<w; w*=2
            xv.append(t&lo)
        s.xv=xv; s.var=[t|(t<<N) for t in xv]; s.Y=lo<<N
        s.nots=[n+k for k,g in enumerate(s.G) if g[0]=='not']
        s.ok=len(s.nots)==1
        if not s.ok: return
        s.yw=s.nots[0]; s.hw=s.G[s.yw-n][1]
        W=list(s.var)
        for g in s.G:
            if g[0]=='not': W.append(s.Y)
            elif g[0]=='and': W.append(W[g[1]]&W[g[2]])
            elif g[0]=='or': W.append(W[g[1]]|W[g[2]])
            else: raise ValueError(g)
        s.W=W; h=W[s.hw]; assert (h&lo)==(h>>N); s.hx=hx=h&lo
        s.o=[0]*len(s.S)
        for k,Sx in enumerate(s.S):
            for u in Sx: s.o[k]|=xv[u]
        real=lambda t:(t&hx)|((t>>N)&~hx&lo)
        s.correct=all(real(W[x])==t for x,t in zip(s.outs,s.o))
        s.c0=all((W[x]&lo)==t for x,t in zip(s.outs,s.o)); s.c1=all((W[x]>>N)==t for x,t in zip(s.outs,s.o))
        s.ess=not s.c0 and not s.c1; s.h0=hx&1
        s.linear=all(len(set(a)&set(b))<=1 for a,b in itertools.combinations(s.S,2))
        s.s=len(s.G); s.base=sum(len(x)-1 for x in s.S)
        s.inputs=list(range(n))+[s.yw]
        s.gatew=[n+k for k,g in enumerate(s.G) if g[0]!='not']
    def pt(s,x,l): return 1<<(x+s.N*l)
    def val(s,w,x,l): return (s.W[w]>>(x+s.N*l))&1
    def down(s,c):  # N-bit mask of {x subset of c}
        m=s.lo
        for v in range(s.n):
            if not (c>>v)&1: m&=~s.xv[v]
        return m
    def hform(s):
        for a,b in itertools.combinations(range(s.n),2):
            if s.hx==(s.xv[a]|s.xv[b]): return a,b
        return None
    def op(s,w): return s.G[w-s.n][0] if w>=s.n else 'in'
    def ch(s,w): return s.G[w-s.n][1:]
class UF:
    def __init__(s,xs): s.p={x:x for x in xs}
    def f(s,x):
        while s.p[x]!=x: x=s.p[x]
        return x
    def u(s,a,b):
        a,b=s.f(a),s.f(b)
        if a==b: return False
        s.p[b]=a; return True
def merges(Lc,Z,atoms,out,restrictR=False):
    """S2.1 union-find. Z bitmask of points, atoms dict key->point index. returns (V set, merge gate list, B fn). asserts lemma steps."""
    W=Lc.W; van=lambda w: (W[w]&Z)==0
    B=lambda w: frozenset(k for k,a in atoms.items() if (W[w]>>a)&1)
    assert van(out), 'F_w not 0 on Z'
    assert len(B(out))==len(atoms), 'atom not a one-point'
    for i in Lc.inputs:
        if van(i): assert len(B(i))<=1, '(L) fails'
    V=set(w for w in range(len(W)) if van(w))
    if restrictR:
        R=set(); st=[out]
        while st:
            w=st.pop()
            if w in R: continue
            R.add(w)
            if w>=Lc.n and w!=Lc.yw:
                for c in Lc.ch(w):
                    if c in V: st.append(c)
        V=R
    uf=UF(atoms.keys()); M=[]
    for w in sorted(V):
        if w<Lc.n or w==Lc.yw: continue
        a,b=Lc.ch(w)
        if Lc.op(w)=='or':
            assert van(a) and van(b)
            if restrictR: assert a in V and b in V
            Ba,Bb=B(a),B(b)
            assert len({uf.f(u) for u in Ba})<=1 and len({uf.f(u) for u in Bb})<=1
            if Ba and Bb and uf.u(next(iter(Ba)),next(iter(Bb))): M.append(w)
        else:
            assert van(a) or van(b), 'AND in V with no child in V'
            if restrictR: assert a in V or b in V
        assert len({uf.f(u) for u in B(w)})<=1
    assert len(M)==len(atoms)-1, ('merge count',len(M),len(atoms))
    return V,M,B
