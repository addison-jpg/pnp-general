import json,sys,itertools
def ana(c):
    n,G=c['n'],c['gates']; X=list(itertools.product([0,1],repeat=n))
    def ev(x,f=None):
        w=list(x)
        for g in G:
            if g[0]=='not': w.append(1-w[g[1]] if f is None else f)
            elif g[0]=='and': w.append(w[g[1]]&w[g[2]])
            else: w.append(w[g[1]]|w[g[2]])
        return w
    T0=[ev(x,0) for x in X]; T1=[ev(x,1) for x in X]
    nk=[k for k,g in enumerate(G) if g[0]=='not'][0]
    dep=[k for k in range(len(G)) if any(a[n+k]!=b[n+k] for a,b in zip(T0,T1)) and k!=nk]
    hw=G[nk][1]
    hones=[x for x,t in zip(X,T0) if t[hw]]
    mins=[[i for i in range(n) if x[i]] for x in hones if not any(y!=x and all(a<=b for a,b in zip(y,x)) for y in hones)]
    ands=[k for k,g in enumerate(G) if g[0]=='and']
    print('sets',c['sets'],'s',len(G),'h minterms',mins,'#y-dep gates',len(dep),'#AND',len(ands),'outs y-dep',[o-n in dep for o in c['outs']])
for l in open(sys.argv[1]):
    if l.startswith('{'): ana(json.loads(l))
