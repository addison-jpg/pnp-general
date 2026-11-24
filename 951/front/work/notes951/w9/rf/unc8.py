import sys,pickle,itertools,json
sys.path.insert(0,'../g1')
import cover, enumcores
sk=pickle.load(open('../g1/cores8.pkl','rb'))
out={}
for S in sk:
    b=sum(len(s)-1 for s in S)
    print(S,b)
    col=set()
    for s in S:
        for p in itertools.combinations(s,2): col.add(p)
    free=[p for p in itertools.combinations(range(8),2) if p not in col]
    for tot in range(b,16):
        j=tot-b
        for ps in itertools.combinations(free,j):
            sets=[list(s) for s in S]+[list(p) for p in ps]
            f=enumcores.canon(8,[frozenset(s) for s in sets])
            if (tot,f) in out: continue
            out[(tot,f)]=(sets,cover.covered(sets))
for tot in range(11,16):
    L=[v for (t,f),v in out.items() if t==tot]
    print(tot,len(L),'uncovered',sum(1 for s,c in L if not c))
unc=[(t,s) for (t,f),(s,c) in out.items() if not c]
json.dump(unc,open('unc8.json','w'))
for t,s in unc:
    if t<=14: print(t,s)
