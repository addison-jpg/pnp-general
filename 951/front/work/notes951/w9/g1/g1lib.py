import json, itertools
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def load(f):
    if f.endswith('.json'): return [norm(json.load(open(f)))]
    return [norm(json.loads(l)) for l in open(f) if l.strip()]
def varmask(n,i):
    m=0
    for x in range(1<<n):
        if (x>>i)&1: m|=1<<x
    return m
_vm={}
def tts(c):
    n=c['n']; full=(1<<(1<<n))-1
    if n not in _vm: _vm[n]=[varmask(n,i) for i in range(n)]
    T=list(_vm[n])
    for g in c['gates']:
        if g[0]=='not': T.append(full^T[g[1]])
        elif g[0]=='and': T.append(T[g[1]]&T[g[2]])
        else: T.append(T[g[1]]|T[g[2]])
    return T
def correct(c,T=None):
    T=T or tts(c); n=c['n']
    for S,o in zip(c['sets'],c['outs']):
        t=0
        for u in S: t|=_vm[n][u]
        if T[o]!=t: return False
    return True
def base(sets): return sum(len(S)-1 for S in sets if len(S)>=2)
def sub(c,T,Z=(),O=(),keep=None):
    """sub-instance: x_Z:=0, x_O:=1, keep outputs in keep (default all). returns (alive set of wire ids, base of restricted family)"""
    n=c['n']; G=c['gates']; full=(1<<(1<<n))-1; vm=_vm[n]
    m=full
    for v in Z: m&=full^vm[v]
    for v in O: m&=vm[v]
    canon={0:'c0',m:'c1'}; alias={}
    for i in range(n):
        t=T[i]&m
        if t not in canon: canon[t]=i
        alias[i]=canon[t]
    for i in range(n,n+len(G)):
        t=T[i]&m
        if t in canon: alias[i]=canon[t]
        else: canon[t]=i; alias[i]=i
    keep=range(len(c['sets'])) if keep is None else keep
    b=0; st=[]
    Zs=set(Z); Os=set(O)
    for w in keep:
        S=c['sets'][w]
        if Os&set(S): continue
        r=[u for u in S if u not in Zs]
        if len(r)>=2: b+=len(r)-1; st.append(alias[c['outs'][w]])
    need=set()
    while st:
        i=st.pop()
        if not isinstance(i,int) or i<n or i in need: continue
        need.add(i); st+=[alias[j] for j in G[i-n][1:]]
    return need,b
def readers(c,v): return [k+c['n'] for k,g in enumerate(c['gates']) if v in g[1:]]
def deg(c,v): return sum(v in S for S in c['sets'])
def iscore(sets,n):
    return all(sum(1 for S in sets if v in S and len(S)>=3)>=2 for v in range(n) if any(v in S for S in sets))
