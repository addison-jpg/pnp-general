# R+ for ALL wires (inputs too): substituting a constant for a wire on any nonempty set of its readers must break an output.
# Also R2 (no duplicate gate functions), R3 (no gate equals an input), R1 (no constant gate), R4 (live), R5' (NOT essential).
# python3 -I research/one-not/tools/kill_tests/f2_rplus_all.py FILE.json [maxreaders=12]
import sys, json, itertools
def tables(n):
    P=1<<n; FULL=(1<<P)-1; X=[]
    for v in range(n):
        m=((1<<(1<<v))-1)<<(1<<v); w=1<<(v+1)
        while w<P: m|=m<<w; w*=2
        X.append(m&FULL)
    return X,FULL
def check(d,maxr=12,verbose=True):
    n=d['n']; S=d['sets']; G=d['gates']; outs=d['outs']; X,FULL=tables(n)
    want=[0]*len(S)
    for i,R in enumerate(S):
        for u in R: want[i]|=X[u]
    def run(sub,notval=None,ret=False):
        W=list(X)
        for k,g in enumerate(G):
            a=[(FULL if sub[(k,s)] else 0) if (k,s) in sub else W[g[s]] for s in range(1,len(g))]
            W.append((FULL^a[0] if notval is None else FULL*notval) if g[0]=='not' else (a[0]&a[1] if g[0]=='and' else a[0]|a[1]))
        return W if ret else all(W[o]==want[i] for i,o in enumerate(outs))
    assert run({}), 'incorrect circuit'
    W=run({},ret=True); viol=[]; skipped=0
    for wire in range(n+len(G)):
        edges=[(j,s) for j,g in enumerate(G) for s in range(1,len(g)) if g[s]==wire]
        if len(edges)>maxr: skipped+=1; continue
        for r in range(1,len(edges)+1):
            for sub in itertools.combinations(edges,r):
                for c in (0,1):
                    if run({e:c for e in sub}): viol.append((wire,[(n+j,s) for j,s in sub],c))
    read={x for g in G for x in g[1:]}
    res=dict(Rplus=len(viol),skipped=skipped,R1=not any(w in (0,FULL) for w in W[n:]),R2=len(set(W[n:]))==len(G),R3=not(set(W[n:])&set(W[:n])),
             R4=all((n+k in read) or (n+k in outs) for k in range(len(G))),R5=(not run({},0)) and (not run({},1)))
    if verbose:
        print(d.get('name'),res)
        for v in viol[:30]: print('  wire',v[0],(G[v[0]-n] if v[0]>=n else 'input'),'edges into',v[1],'constant',v[2])
    return res,viol
if __name__=='__main__': check(json.load(open(sys.argv[1])),int(sys.argv[2]) if len(sys.argv)>2 else 12)
