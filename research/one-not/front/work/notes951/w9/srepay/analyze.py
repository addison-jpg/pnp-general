# S-repay analysis: full lifted single-domain menus (S2.3 + circuit-dependent extension), ClassFrac LP, collisions/outside.
# Usage: python3 analyze.py file.json [file2.json ...]   (jsonl lines also accepted: file.jsonl)
import sys, itertools, json, collections
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
sys.path.insert(0,F+'w9/jcut'); sys.path.insert(0,F+'w9/s')
from bt import TT, norm
from chk2 import lp

def popc(m): return bin(m).count('1')

def info(c):
    T=TT(c); n=T.n
    GL=[g for g in range(n,T.W) if g!=T.Ni]          # gates of the lifted monotone circuit M
    T.GL=GL; T.gi={g:i for i,g in enumerate(GL)}
    return T

def essential(T):
    c=T.c; ok0=all(T.w[0][o]==t for o,t in zip(c['outs'],T.o)); ok1=all(T.w[1][o]==t for o,t in zip(c['outs'],T.o))
    return (not ok0) and (not ok1)

def menu(T,wi,full=True):
    """all classes of set wi: dict mask -> descriptor.  mask = bitmask over T.GL positions.
       type 0: Z=Z^0_w, atoms (p,0) p∩S={u} F_w(p,0)=1 (minimal), <=1 level-1 atom (e_u,1); plus maximal-atom classes.
       type 1: Z=down(c,1), F_w(c,1)=0, c∩S=∅ (all such c), atoms (e_u,1) or minimal (p,0), p ⊆ c+u, F_w(p,0)=1; plus max atoms (c+e_u,1)."""
    c=T.c; n=T.n; R=c['sets'][wi]; o=c['outs'][wi]; F0=T.w[0][o]; F1=T.w[1][o]; no=T.FULL^T.o[wi]
    rest=[v for v in range(n) if v not in R]; zR=sum(1<<v for v in rest); d=len(R)-1
    GL=T.GL
    def bitvec(at):  # mask of gates that are 1 at atom
        p,l=at; m=0
        for i,g in enumerate(GL):
            if (T.w[l][g]>>p)&1: m|=1<<i
        return m
    cache={}
    def bv(at):
        if at not in cache: cache[at]=bitvec(at)
        return cache[at]
    def cls(base,atoms):
        vs=[bv(a) for a in atoms]
        # gates in base that are 1 on >=2 atoms
        one=0; two=0
        for v in vs:
            two|=one&v; one|=v
        return base&two
    out={}
    def add(mask,desc):
        assert popc(mask)>=d, ('SHORT CLASS',wi,desc,popc(mask))
        if mask not in out: out[mask]=desc
    def subsets(vs):
        for r in range(len(vs)+1):
            for zz in itertools.combinations(vs,r): yield sum(1<<v for v in zz)
    def minimal(pts):
        pts=sorted(pts,key=popc); res=[]
        for p in pts:
            if not any((q&p)==q for q in res): res.append(p)
        return res
    # ---- type 0
    base0=0
    for i,g in enumerate(GL):
        if (T.w[0][g]&no)==0: base0|=1<<i
    opts={}
    for u in R:
        pts=[(1<<u)|t for t in subsets(rest) if (F0>>((1<<u)|t))&1]
        opts[u]=[(p,0) for p in minimal(pts)]+[(1<<u,1)]
    for cb in itertools.product(*[opts[u] for u in R]):
        if sum(a[1] for a in cb)>1: continue
        add(cls(base0,cb),('0',cb))
    if full:
        mx=[(zR|1<<u,0) for u in R]
        if all((F0>>a[0])&1 for a in mx): add(cls(base0,mx),('0max',tuple(mx)))
        for j,u0 in enumerate(R):
            cb=[a for a in mx]; cb[j]=(zR|1<<u0,1)
            if all((T.w[l][o]>>p)&1 for p,l in cb): add(cls(base0,cb),('0max',tuple(cb)))
    # ---- type 1
    for cc in subsets(rest):
        if (F1>>cc)&1: continue
        base1=0
        for i,g in enumerate(GL):
            if not (T.w[1][g]>>cc)&1: base1|=1<<i
        cv=[v for v in rest if cc>>v&1]
        o1={}
        for u in R:
            pts=[(1<<u)|t for t in subsets(cv) if (F0>>((1<<u)|t))&1]
            o1[u]=[(1<<u,1)]+[(p,0) for p in minimal(pts)]
        for cb in itertools.product(*[o1[u] for u in R]):
            add(cls(base1,cb),('1',cc,cb))
        if full:
            mx=[(cc|1<<u,1) for u in R]; add(cls(base1,mx),('1max',cc,tuple(mx)))
    return out

def maximal(masks):
    ms=sorted(set(masks),key=popc,reverse=True); res=[]
    for m in ms:
        if not any((m&r)==m for r in res): res.append(m)
    return res
def minimal_m(masks):
    ms=sorted(set(masks),key=popc); res=[]
    for m in ms:
        if not any((r&m)==r for r in res): res.append(m)
    return res

def maxflow(dem,cls):
    # bipartite b-matching: set w demands dem[w] from gates in cls[w] (bitmask), gate cap 1. simple augmenting paths
    gates=sorted({i for m in cls for i in range(m.bit_length()) if m>>i&1})
    owner={}  # gate -> set
    load=[0]*len(dem)
    def aug(w,seen):
        for i in gates:
            if not (cls[w]>>i)&1 or i in seen: continue
            seen.add(i)
            if i not in owner: owner[i]=w; return True
            w2=owner[i]
            if aug(w2,seen): owner[i]=w; return True
        return False
    f=0
    for w in range(len(dem)):
        for _ in range(dem[w]):
            if aug(w,set()): f+=1
            else: break
    return f

def joint_merges(T,sets_idx=None):
    # joint world-1 union-find at Z={(0,1)}, atoms (e_u,1) for all u in the union of the sets
    c=T.c; n=T.n; sets=c['sets'] if sets_idx is None else [c['sets'][i] for i in sets_idx]
    U=sorted({u for S in sets for u in S})
    par={u:u for u in U}
    def f(u):
        while par[u]!=u: u=par[u]
        return u
    merges=[]
    W1=T.w[1]
    B={}
    for v in range(n): B[v]={v} if v in U else set()
    for k,g in enumerate(T.G):
        gid=n+k
        if g[0]=='not': continue
        if W1[gid]&1: continue   # value 1 at (0,1): not in V
        Bg={u for u in U if (W1[gid]>>(1<<u))&1}
        if g[0]=='or':
            roots={f(u) for u in Bg}
            if len(roots)>=2:
                r=sorted(roots)
                for x in r[1:]: par[x]=r[0]
                merges.append((gid,len(roots)-1))
    comps=len({f(u) for u in U})
    return sum(m for _,m in merges), len(U)-comps, merges

def analyze(name,c,verbose=True,lpdo=True):
    c=norm(c); T=info(c); n=T.n; S=c['sets']; dem=[len(x)-1 for x in S]; base=sum(dem)
    assert T.correct(), name+' INCORRECT'
    sM=len(T.GL); s=len(c['gates'])
    menus=[menu(T,wi) for wi in range(len(S))]
    allm=[list(m.keys()) for m in menus]
    mins=[min(popc(m) for m in ms) for ms in allm]
    res=dict(name=name,n=n,s=s,base=base,ess=essential(T),h=T.h,menu=[len(m) for m in allm],minclass=mins)
    res['V2slack']=sM-sum(mins)     # (#M gates outside) - (multiplicity collisions) for the smallest classes
    if lpdo:
        Lmax,pi,lam=lp(dem,[[frozenset(i for i in range(m.bit_length()) if m>>i&1) for m in maximal(ms)] for ms in allm])
        Lmin,_,_=lp(dem,[[frozenset(i for i in range(m.bit_length()) if m>>i&1) for m in minimal_m(ms)] for ms in allm])
        res['Lmax']=round(Lmax,4); res['Lmin']=round(Lmin,4)
    # V1: best integral choice: maximise out - def = (sM-|U|) - (base - flow)
    if len(S)==2:
        best=None
        mn0=minimal_m(allm[0]); mn1=minimal_m(allm[1])
        for a in allm[0]:
            for b in allm[1]:
                U=popc(a|b); fl=min(base,U); sl=(sM-U)-(base-fl)
                if best is None or sl>best[0]: best=(sl,a,b)
        res['V1slack']=best[0]
        # min collisions over pairs (integral), and its out
        mc=min((popc(a&b),sM-popc(a|b)) for a in allm[0] for b in allm[1])
        res['mincoll']=mc
    jm,need,_=joint_merges(T)
    res['joint_merges']=jm; res['joint_need']=need
    if verbose: print(json.dumps(res))
    return res,T,menus

if __name__=='__main__':
    for f in sys.argv[1:]:
        if f.endswith('.jsonl'):
            for i,l in enumerate(open(f)):
                if l.strip(): analyze(f+':%d'%i,json.loads(l))
        else: analyze(f,json.load(open(f)))

def world1_merges(T):
    """per-set and joint union-find at Z={(0,1)}, unit atoms (e_u,1).  Returns dict with
       J (joint merge gates), M[w] (per-set merge gates), X (joint merges in no M_w), coll = Σ(k_g-1)^+, nonjoint = Σ_{j=0} k,
       cyc = base - (|V'| - c), V (gates of M vanishing at (0,1))."""
    c=T.c; n=T.n; S=c['sets']; W1=T.w[1]
    Vp=sorted({u for s_ in S for u in s_})
    def uf(atoms):
        par={u:u for u in atoms}
        def f(u):
            while par[u]!=u: u=par[u]
            return u
        return par,f
    jp,jf=uf(Vp); sp=[uf(s_) for s_ in S]
    J=[];M=[[] for _ in S];V=[]
    Bw={}
    for v in range(n): Bw[v]={v} if v in Vp else set()
    for k,g in enumerate(T.G):
        gid=n+k
        if g[0]=='not': Bw[gid]=None; continue
        if W1[gid]&1: Bw[gid]=None; continue
        V.append(gid)
        Bg={u for u in Vp if (W1[gid]>>(1<<u))&1}; Bw[gid]=Bg
        if g[0]!='or': continue
        Bs,Bt=Bw[g[1]],Bw[g[2]]
        assert Bs is not None and Bt is not None
        # joint
        if Bs and Bt:
            r1=jf(next(iter(Bs))); r2=jf(next(iter(Bt)))
            if r1!=r2: jp[r2]=r1; J.append(gid)
        for wi,s_ in enumerate(S):
            par,f=sp[wi]
            a=[u for u in Bs if u in s_]; b=[u for u in Bt if u in s_]
            if a and b:
                r1=f(a[0]); r2=f(b[0])
                if r1!=r2: par[r2]=r1; M[wi].append(gid)
    roots={jf(u) for u in Vp}
    # components of hypergraph
    cp,cf=uf(Vp)
    for s_ in S:
        for u in s_[1:]:
            r1,r2=cf(s_[0]),cf(u)
            if r1!=r2: cp[r2]=r1
    comp=len({cf(u) for u in Vp})
    base=sum(len(s_)-1 for s_ in S)
    cnt=collections.Counter(g for m in M for g in m)
    allM=set(cnt)
    X=[g for g in J if g not in allM]
    coll=sum(k-1 for k in cnt.values() if k>1)
    nonjoint=sum(1 for g,k in cnt.items() if g not in set(J))
    return dict(J=J,M=M,X=X,coll=coll,nonjoint=nonjoint,cyc=base-(len(Vp)-comp),V=V,
                Mfull=[len(m)==len(s_)-1 for m,s_ in zip(M,S)],nM=len(T.GL))

def gdesc(T,g):
    G=T.G[g-T.n]; nd=T.w[0][g]!=T.w[1][g]
    return '%d=%s(%s)%s'%(g,G[0],','.join(map(str,G[1:])),'*' if nd else '')
