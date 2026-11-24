import json,sys,glob,itertools,random,os,time
import numpy as np
F='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad'
def load(f):
    if f.endswith('.jsonl'): return [(f'{f}#{i}',json.loads(l)) for i,l in enumerate(open(f)) if l.strip()]
    d=json.load(open(f))
    if isinstance(d,list): return [(f'{f}#{i}',x) for i,x in enumerate(d) if isinstance(x,dict) and 'gates' in x]
    return [(f,d)] if 'gates' in d else []
def tables(c):
    n=c['n'];G=c['gates'];P=1<<n;full=(1<<P)-1
    T=[]
    for v in range(n):
        t=0
        for p in range(P):
            if p>>v&1: t|=1<<p
        T.append(t)
    for g in G:
        if g[0]=='not': T.append(full^T[g[1]])
        elif g[0]=='and': T.append(T[g[1]]&T[g[2]])
        else: T.append(T[g[1]]|T[g[2]])
    return T
def correct(c,T):
    for S,o in zip(c['sets'],c['outs']):
        f=0
        for v in S: f|=T[v]
        if T[o]!=f: return False
    return True
def Bfamily(c,T,w):
    n=c['n'];G=c['gates'];S=c['sets'][w];Sm=sum(1<<v for v in S)
    rest=[v for v in range(n) if v not in S]
    fam=set();anom=0
    for r in range(1<<len(rest)):
        z=0
        for i,v in enumerate(rest):
            if r>>i&1: z|=1<<v
        par={u:u for u in S}
        def find(u):
            while par[u]!=u: par[u]=par[par[u]];u=par[u]
            return u
        B={}
        for v in S:
            if not T[v]>>z&1: B[v]=frozenset([v])   # zero at z always
        M=0;cnt=0
        for k,g in enumerate(G):
            i=n+k
            if T[i]>>z&1: continue
            B[i]=frozenset(u for u in S if T[i]>>(z|1<<u)&1)
            if g[0]=='or':
                a=B.get(g[1]);b=B.get(g[2])
                if a is not None and b is not None and a and b:
                    rs={find(u) for u in a|b}
                    if len(rs)>1:
                        if len(rs)>2: anom+=1
                        rs=sorted(rs)
                        for x in rs[1:]: par[x]=rs[0]
                        M|=1<<k;cnt+=1
        if cnt!=len(S)-1: anom+=1
        fam.add(M)
    return sorted(fam),anom
def exchange(fam):
    fs=set(fam)
    for b1 in fam:
        for b2 in fam:
            d=b1&~b2
            if not d: continue
            e=b2&~b1
            x=d
            while x:
                lx=x&-x;x^=lx
                ok=False;y=e
                while y:
                    ly=y&-y;y^=ly
                    if (b1^lx)|ly in fs: ok=True;break
                if not ok: return False
    return True
def rankmat(fam,g):
    return np.array([[ (b>>k)&1 for k in range(g)] for b in fam],dtype=np.float32)
def ranks(Bm,Am):
    out=np.empty(len(Am),dtype=np.int32)
    for i in range(0,len(Am),4096):
        out[i:i+4096]=(Am[i:i+4096]@Bm.T).max(axis=1).astype(np.int32)
    return out
def run(name,c,log):
    n=c['n'];g=len(c['gates']);k=len(c['sets'])
    if n>12: return None
    T=tables(c);cor=correct(c,T)
    fams=[];anoms=0;mat=[]
    for w in range(k):
        f,a=Bfamily(c,T,w);fams.append(f);anoms+=a;mat.append(exchange(f))
    res=dict(name=name,n=n,gates=g,k=k,correct=cor,nb=[len(f) for f in fams],matroid=mat,anom=anoms,rk=[max(bin(b).count('1') for b in f) for f in fams])
    # union test
    Bms=[rankmat(f,g) for f in fams]
    rG=res['rk']
    if g<=18:
        Am=((np.arange(1<<g)[:,None]>>np.arange(g))&1).astype(np.float32);mode='exhaustive'
    else:
        rnd=random.Random(1);rows=set()
        for _ in range(20000):
            d=rnd.choice([.1,.3,.5,.7,.9]);rows.add(sum(1<<j for j in range(g) if rnd.random()<d))
        # unions of M_z's
        tot=1
        for f in fams: tot*=len(f)+1
        if tot<=20000:
            for combo in itertools.product(*[[0]+f for f in fams]):
                a=0
                for b in combo:a|=b
                rows.add(a)
        else:
            for _ in range(20000):
                a=0
                for f in fams:
                    if rnd.random()<.8:a|=rnd.choice(f)
                rows.add(a)
        rows=list(rows);Am=np.array([[ (a>>j)&1 for j in range(g)] for a in rows],dtype=np.float32);mode=f'sampled({len(rows)})'
    tot=np.zeros(len(Am),dtype=np.int32)
    for w in range(k): tot+=rG[w]-ranks(Bms[w],Am)
    comp=g-Am.sum(axis=1).astype(np.int32)
    viol=np.where(tot>comp)[0]
    res['mode']=mode;res['nA']=len(Am);res['viol']=len(viol)
    if len(viol):
        i=viol[np.argmax((tot-comp)[viol])]
        A=[j for j in range(g) if Am[i,j]]
        res['worst']=dict(A=A,sum=int(tot[i]),Gminus=int(comp[i]),per_set=[int(rG[w]-ranks(Bms[w],Am[i:i+1])[0]) for w in range(k)])
    return res
if __name__=='__main__':
    files=sys.argv[1:]
    cs=[]
    for f in files: cs+=load(f)
    for name,c in cs:
        t=time.time();r=run(name,c,None)
        if r is None: print(json.dumps(dict(name=name,n=c['n'],skipped='n>12')),flush=True);continue
        r['sec']=round(time.time()-t,1);print(json.dumps(r),flush=True)
