import sys
from g1lib import *
def stats(c):
    T=tts(c); n=c['n']; S=c['sets']; s=len(c['gates']); b=base(S)
    assert correct(c,T)
    r=dict(n=n,s=s,base=b,slack=s-b)
    d0=[];d1=[];rd=[]
    for v in range(n):
        dg=deg(c,v)
        if dg==0: continue
        a,_=sub(c,T,Z=[v]); d0.append((s-len(a))-dg)
        a,_=sub(c,T,O=[v]); d1.append((s-len(a))-sum(len(w)-1 for w in S if v in w))
        rd.append(len(readers(c,v))-dg)
    r['sum0']=sum(d0); r['max0']=max(d0); r['sum1']=sum(d1); r['max1']=max(d1); r['sumrd']=sum(rd); r['nv']=len(d0)
    dl=[]
    for w in range(len(S)):
        a,bb=sub(c,T,keep=[x for x in range(len(S)) if x!=w]); dl.append((s-len(a))-(len(S[w])-1))
    r['maxdel']=max(dl); r['sumdel']=sum(dl)
    return r
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[c for c in load(f) if c['n']<=12]
        R=[stats(c) for c in cs]
        if len(R)<=4:
            for r in R: print(f.split('/')[-1],r)
        else:
            print(f.split('/')[-1],len(R),'slack min',min(r['slack'] for r in R),
              '| min (sum0 - slack*?) : min sum0',min(r['sum0'] for r in R),'min sum0+nv',min(r['sum0']+r['nv'] for r in R),
              'min max0',min(r['max0'] for r in R),'min sum1',min(r['sum1'] for r in R),'min max1',min(r['max1'] for r in R),
              'min maxdel',min(r['maxdel'] for r in R),'min(max(max0,max1))',min(max(r['max0'],r['max1']) for r in R),
              'min (sum0 - nv*slack)',min(r['sum0']-r['nv']*r['slack'] for r in R),'max',max(r['sum0']-r['nv']*r['slack'] for r in R))
