# R+ check at a fixed circuit: for every gate, every nonempty set of its out-edges and each constant c,
# substituting c on those edges must break some output.  Prints the violations (removable edge sets).
# python3 -I one-not/tools/kill_tests/f2_rplus.py FILE.json
import sys, json, itertools
def rplus(d, verbose=True):
    n=d['n']; S=d['sets']; G=d['gates']; outs=d['outs']; P=1<<n; FULL=(1<<P)-1
    X=[]
    for v in range(n):
        blk=(1<<(1<<v))-1; m=0; per=1<<(v+1)
        # pattern: 2^v zeros then 2^v ones, repeated
        unit=blk<<(1<<v); m=unit
        w=per
        while w<P: m|=m<<w; w*=2
        X.append(m&FULL)
    want=[0]*len(S)
    for i,R in enumerate(S):
        for u in R: want[i]|=X[u]
    def run(sub):
        W=list(X)
        for k,g in enumerate(G):
            a=[ (FULL if sub[(k,s)] else 0) if (k,s) in sub else W[g[s]] for s in range(1,len(g))]
            W.append(FULL^a[0] if g[0]=='not' else (a[0]&a[1] if g[0]=='and' else a[0]|a[1]))
        return all(W[o]==want[i] for i,o in enumerate(outs))
    assert run({}), 'incorrect circuit'
    viol=[]
    for k in range(len(G)):
        edges=[(j,s) for j,g in enumerate(G) for s in range(1,len(g)) if g[s]==n+k]
        for r in range(1,len(edges)+1):
            for sub in itertools.combinations(edges,r):
                for c in (0,1):
                    if run({e:c for e in sub}): viol.append((n+k,G[k],[(n+j,s) for j,s in sub],c))
    if verbose:
        print(d.get('name'),'R+ violations:',len(viol))
        for v in viol[:40]: print('  gate',v[0],v[1],'edges into',v[2],'constant',v[3])
    return viol
if __name__=='__main__': rplus(json.load(open(sys.argv[1])))
