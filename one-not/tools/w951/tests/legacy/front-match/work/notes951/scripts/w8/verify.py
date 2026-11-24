import sys, json, itertools, os
def evalN(n,G,x,force=None):
    w=list(x)
    for gt in G:
        if gt[0]=='not': w.append(1-w[gt[1]] if force is None else force)
        elif gt[0]=='and': w.append(w[gt[1]]&w[gt[2]])
        else: w.append(w[gt[1]]|w[gt[2]])
    return w
def verify(c):
    n,G,S=c['n'],c['gates'],c['sets']; tabs=[[] for _ in range(n+len(G))]; ok=c0=c1=True
    for x in itertools.product([0,1],repeat=n):
        w=evalN(n,G,x); w0=evalN(n,G,x,0); w1=evalN(n,G,x,1)
        for i in range(len(w)): tabs[i].append(w[i])
        for o,st in zip(c['outs'],S):
            f=int(any(x[v] for v in st)); ok&=w[o]==f; c0&=w0[o]==f; c1&=w1[o]==f
    tt=[tuple(t) for t in tabs]
    read=set(j for gt in G for j in gt[1:])|set(c['outs'])
    return dict(correct=ok,C0=c0,C1=c1,clean=len(set(tt))==len(tt) and all(0<sum(t)<len(t) for t in tt),read=all(n+k in read for k in range(len(G))),s=len(G),base=sum(len(s)-1 for s in S))
if __name__=='__main__':
    c=json.load(open(sys.argv[1])); print(verify(c))
    here=os.getcwd(); sys.path.insert(0,'../chk'); sys.argv=sys.argv[:1]
    src=open('../chk/hallcheck.py').read().split('H=Counter()')[0]; os.chdir('../chk'); exec(src)
    Ds=canon(c); dem=[len(s)-1 for s in c['sets']]
    print('canonical cnt',Ds,'union',len(set().union(*map(set,Ds))),'bmatch',bmatch(Ds,dem),'base',sum(dem))
