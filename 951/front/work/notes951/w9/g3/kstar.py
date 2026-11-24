import sys,itertools
from star import load,tts
def jset(ttl,fams,full):
    """ttl: list of gate tts; fams: list of set-tts (sizes>=2). returns set of indices in J"""
    J=set()
    pairs=list(itertools.combinations(range(len(fams)),2))
    for k,g in enumerate(ttl):
        for a,b in pairs:
            if g & ~(fams[a]&fams[b]) & full==0 or (fams[a]|fams[b]) & ~g==0: J.add(k);break
    return J
def restrict(t,n,v,b):
    r=0;j=0
    for x in range(1<<n):
        if (x>>v&1)==b:
            if t>>x&1: r|=1<<j
            j+=1
    return r
def kstar(c):
    n=c['n'];var,w,full=tts(c);G=c['gates']
    sets=[S for S in c['sets'] if len(S)>=2]
    A=[0]*len(sets)
    for i,S in enumerate(sets):
        for u in S: A[i]|=var[u]
    base=sum(len(S)-1 for S in sets)
    gt=w[n:]
    nonJ=len(gt)-len(jset(gt,A,full))
    res=[]
    fullr=(1<<(1<<(n-1)))-1
    for v in range(n):
        for b in (0,1):
            if b==0: S2=[[u for u in S if u!=v] for S in sets]
            else: S2=[S for S in sets if v not in S]
            S2=[S for S in S2 if len(S)>=2]
            base2=sum(len(S)-1 for S in S2)
            rw=[restrict(t,n,v,b) for t in w]
            varr=set(rw[u] for u in range(n) if u!=v)
            alive=[]
            for k,g in enumerate(G):
                t=rw[n+k]
                if t==0 or t==fullr or t in varr: continue
                if g[0]=='not': alive.append(t);continue
                if t==rw[g[1]] or t==rw[g[2]]: continue
                alive.append(t)
            # set tts on restricted cube
            A2=[]
            for S in S2:
                a=0
                for u in S: a|=rw[u]
                A2.append(a)
            nonJ2=len(alive)-len(jset(alive,A2,fullr))
            res.append((nonJ-nonJ2-(base-base2),v,b,nonJ2,base2))
    return nonJ,base,max(res),res
if __name__=='__main__':
    lim=int(sys.argv[1]) if sys.argv[1].isdigit() else None
    files=sys.argv[2:] if lim is not None else sys.argv[1:]
    for f in files:
        cs=load(f)[:lim] if lim else load(f)
        worst=None;neg=0
        for c in cs:
            nonJ,base,best,res=kstar(c)
            if best[0]<0: neg+=1
            if worst is None or best[0]<worst[0]: worst=(best[0],nonJ,base,best)
        print(f.split('scratchpad/')[-1],len(cs),'K*fail',neg,'worst',worst,flush=True)
