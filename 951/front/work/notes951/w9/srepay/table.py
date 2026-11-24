# summary table for a list of circuit files (json / jsonl)
import sys, json, collections
files=sys.argv[1:]; sys.argv=['x']
from analyze import *
from rest import decomp
def rows(f):
    if f.endswith('.jsonl'):
        for i,l in enumerate(open(f)):
            if l.strip(): yield f.split('/')[-1]+':%d'%i, json.loads(l)
    else: yield f.split('/')[-1], json.load(open(f))
out=[]
for f in files:
    for name,c in rows(f):
        r,T,men=analyze(name,c,verbose=False)
        d=decomp(T); w=world1_merges(T)
        clean=len({T.w['real'][g] for g in range(T.W)})==T.W
        hm=[x for x in range(1<<T.n) if (T.h>>x)&1]; mins=[x for x in hm if not any((y&x)==y and y!=x for y in hm)]
        th2=all(bin(x).count('1')==2 for x in mins) and len(mins)==T.n*(T.n-1)//2
        out.append(dict(name=name,s=r['s'],base=r['base'],ess=r['ess'],clean=clean,hTh2=th2,Lmax=r['Lmax'],Lmin=r['Lmin'],
            minclass=r['minclass'],V2=r['V2slack'],V1=r.get('V1slack'),J=d['J'],AND=d['AND'],HI=d['HI'],RED=d['RED'],cyc=d['cyc'],coll=w['coll'],X=len(w['X'])))
for o in out: print(json.dumps(o))
