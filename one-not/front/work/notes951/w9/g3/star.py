import json,sys,itertools
def norm(c):
    c['gates']=[['not',g[1]] if g[0]=='not' else list(g) for g in c['gates']]; return c
def load(f):
    if f.endswith('.json'): return [norm(json.load(open(f)))]
    return [norm(json.loads(l)) for l in open(f) if l.strip()]
def tts(c):
    n=c['n'];M=1<<n;full=(1<<M)-1
    var=[]
    for v in range(n):
        t=0
        for x in range(M):
            if x>>v&1: t|=1<<x
        var.append(t)
    w=list(var)
    for g in c['gates']:
        if g[0]=='not': w.append(full^w[g[1]])
        elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
        else: w.append(w[g[1]]|w[g[2]])
    return var,w,full
def analyse(c):
    n=c['n'];var,w,full=tts(c)
    sets=[S for S in c['sets'] if len(S)>=2]
    A=[0]*len(c['sets'])
    for i,S in enumerate(c['sets']):
        for u in S: A[i]|=var[u]
    ok=all(w[o]==A[i] for i,o in enumerate(c['outs']))
    idx=[i for i,S in enumerate(c['sets']) if len(S)>=2]
    base=sum(len(c['sets'][i])-1 for i in idx)
    pairs=[(a,b) for a in idx for b in idx if a<b]
    JL=set();JU=set()
    for k in range(n,len(w)):
        g=w[k]
        for a,b in pairs:
            if g & ~(A[a]&A[b]) & full==0: JL.add(k)
            if (A[a]|A[b]) & ~g ==0: JU.add(k)
    s=len(c['gates']); cnt=s-len(JL|JU)
    mono=all(g[0]!='not' for g in c['gates'])
    return dict(ok=ok,s=s,base=base,JL=len(JL),JU=len(JU),cnt=cnt,slack=cnt-base,mono=mono)
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=load(f); worst=None; bad=0;nok=0
        for c in cs:
            r=analyse(c)
            if not r['ok']: nok+=1; continue
            if r['slack']<0: bad+=1
            if worst is None or r['slack']<worst['slack']: worst=r
        print(f.split('scratchpad/')[-1],len(cs),'notok',nok,'viol',bad,'worst',worst)
