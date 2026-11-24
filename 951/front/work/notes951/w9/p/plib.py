# independent toolkit for task P (Pi* classes). Truth tables as python ints over 2^n points.
import json, glob, sys
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def alldata():
    out=[]
    fs=sorted(glob.glob(F+'w8/cx*.json'))+[F+'w8b/cxr.json',F+'w9/fb/cfgI.json']+sorted(glob.glob(F+'w9/fc/*.json'))+sorted(glob.glob(F+'w9/tw/*.json'))+sorted(glob.glob(F+'w9/g3/*.json'))
    for f in fs: out.append((f.replace(F,''),norm(json.load(open(f)))))
    for f in ['w7/badT.jsonl','w7/bad.jsonl','chk/c.jsonl']:
        for i,l in enumerate(open(F+f)):
            if l.strip(): out.append((f+':%d'%i,norm(json.loads(l))))
    return out
class C:
    def __init__(s,c):
        s.c=c; n=s.n=c['n']; P=s.P=1<<n; FULL=s.FULL=(1<<P)-1
        s.var=[]
        for v in range(n):
            blk=(1<<(1<<v))-1; m=0; per=1<<(v+1)
            # pattern: zeros for 2^v, ones for 2^v, repeated
            unit=blk<<(1<<v); m=0
            for k in range(0,P,per): m|=unit<<k
            s.var.append(m)
        G=s.G=c['gates']; s.W=n+len(G)
        s.Ni=None
        for k,g in enumerate(G):
            if g[0]=='not':
                assert s.Ni is None; s.Ni=n+k
        def ev(mode):
            w=list(s.var)
            for g in G:
                if g[0]=='not': w.append(FULL^w[g[1]] if mode=='r' else (0 if mode==0 else FULL))
                elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
                elif g[0]=='or': w.append(w[g[1]]|w[g[2]])
                else: raise ValueError(g)
            return w
        s.r=ev('r'); s.c0=ev(0); s.c1=ev(1)
        s.h=s.r[G[s.Ni-n][1]] if s.Ni is not None else 0
        s.U1=s.h; s.U0=FULL^s.h
        s.sets=c['sets']; s.m=len(s.sets); s.outs=c['outs']
        s.o=[]
        for S in s.sets:
            t=0
            for u in S: t|=s.var[u]
            s.o.append(t)
        s.d=[len(S)-1 for S in s.sets]; s.base=sum(s.d); s.s=len(G)
        s.zS=[sum(1<<v for v in range(n) if v not in S) for S in s.sets]
        s.hard=[bool(s.h>>z&1) for z in s.zS]
        s.heavy=[bool(s.h>>(1<<u)&1) for u in range(n)]
    def at(s,tt,x): return tt>>x&1
    def correct(s): return all(s.r[o]==t for o,t in zip(s.outs,s.o))
    def c0ok(s): return all(s.c0[o]==t for o,t in zip(s.outs,s.o))
    def c1ok(s): return all(s.c1[o]==t for o,t in zip(s.outs,s.o))
    def clean(s):
        seen={0,s.FULL}
        for t in s.r:
            if t in seen: return False
            seen.add(t)
        return True
    def live(s):
        read=set(s.outs)
        for g in s.G:
            read.update(g[1:])
        return all(g in read for g in range(s.n,s.W))
    def lightsets(s):
        pass
    def status(s):
        return dict(n=s.n,s=s.s,base=s.base,correct=s.correct(),clean=s.clean(),live=s.live(),ess=(not s.c0ok()) and (not s.c1ok()),h0=(s.h&1)==0,hard=s.hard)
    # ---------- classes ----------
    def classes(s):
        n=s.n; r=s.r; FULL=s.FULL; U0=s.U0; U1=s.U1
        K={k:[set() for _ in range(s.m)] for k in ('Dr','DrS','Pr','D0','P0','D1')}
        for i,S in enumerate(s.sets):
            o=s.o[i]
            for g in range(n,s.W):
                t=r[g]
                if t&~o==0:
                    if sum(t>>(1<<u)&1 for u in S)>=2: K['Dr'][i].add(g)      # T3 def: g(e_u)=1 for >=2 u
                    if sum((s.var[u]&~t)==0 for u in S)>=2: K['DrS'][i].add(g) # strong (cls2) def: x_u<=g
                if o&~t==0 and t!=FULL and all(s.o[j]&~t for j in range(s.m) if j!=i): K['Pr'][i].add(g)
                # world 1 (U0), all sets
                if t&U0&~o==0:
                    if sum((not s.heavy[u]) and (t>>(1<<u)&1) for u in S)>=2: K['D1'][i].add(g)
                if s.hard[i]:
                    if t&U1&~o==0:
                        if sum(bool(s.var[u]&U1) and (s.var[u]&U1&~t)==0 for u in S)>=2: K['D0'][i].add(g)
                    if o&U1&~t==0 and (t&U1)!=U1 and all(s.o[j]&U1&~t for j in range(s.m) if j!=i and s.hard[j]): K['P0'][i].add(g)
        return K
    def minterms(s):
        # minterms of h as bitmasks (minimal points with h=1)
        res=[]
        for x in range(s.P):
            if s.h>>x&1:
                ok=True; y=x
                while y:
                    b=y&-y
                    if s.h>>(x^b)&1: ok=False;break
                    y^=b
                if ok: res.append(x)
        return res
    def cnt_z(s,i,z):
        """B3 system Sigma(z): gates with g(z)=0 and g(z+e_u)=1 for >=2 u in S_i"""
        S=s.sets[i]; assert all(not z>>u&1 for u in S)
        return {g for g in range(s.n,s.W) if not s.r[g]>>z&1 and sum(s.r[g]>>(z|1<<u)&1 for u in S)>=2}
def match(dem,adj):
    mt={}
    def aug(w,seen):
        for g in adj[w]:
            if g in seen: continue
            seen.add(g)
            if g not in mt or aug(mt[g],seen):
                mt[g]=w; return True
        return False
    tot=0
    for w,d in enumerate(dem):
        for _ in range(d):
            if aug(w,set()): tot+=1
    return tot
def pistar(K,i,names=('Dr','Pr','D0','P0','D1')):
    return set().union(*[K[k][i] for k in names])
class B:
    """circuit builder"""
    def __init__(s,n): s.n=n; s.G=[]; s.memo={}
    def g(s,op,a,b=None):
        key=(op,)+tuple(sorted([a,b])) if b is not None else (op,a)
        if key in s.memo: return s.memo[key]
        s.G.append([op,a,b] if op!='not' else ['not',a]); s.memo[key]=s.n+len(s.G)-1; return s.memo[key]
    def AND(s,ws):
        w=ws[0]
        for v in ws[1:]: w=s.g('and',w,v)
        return w
    def OR(s,ws):
        w=ws[0]
        for v in ws[1:]: w=s.g('or',w,v)
        return w
    def out(s,sets,outs): return dict(n=s.n,sets=sets,gates=s.G,outs=outs)
def d0m(T,i):
    """per-minterm world-0 classes: dict minterm -> {g : g<=o_i on cone(M), g(1_M+e_u)=1 for >=2 u in S_i}, M avoiding S_i"""
    S=T.sets[i]; res={}
    for M in T.minterms():
        if any(M>>u&1 for u in S): continue
        cone=T.FULL
        for v in range(T.n):
            if M>>v&1: cone&=T.var[v]
        res[M]={g for g in range(T.n,T.W) if (T.r[g]&cone&~T.o[i])==0 and sum(T.r[g]>>(M|1<<u)&1 for u in S)>=2}
    return res
def pi2(T,K,i):
    U=pistar(K,i)
    if T.hard[i]:
        for M,s in d0m(T,i).items(): U|=s
    return U
