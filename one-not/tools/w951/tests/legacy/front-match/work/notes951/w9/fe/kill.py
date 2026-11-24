# restriction-induction test: for x_v=b, size s' of the cleaned restricted circuit; reducible iff s-s' >= base loss
import sys, json
sys.path.insert(0,'../fa')
from lib import load, ev
def restr(c,v,b):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']
    pts=[x for x in range(1<<n) if ((x>>v)&1)==b]
    T=[ev(n,G,[(x>>i)&1 for i in range(n)]) for x in pts]
    W=n+len(G); tab=[tuple(T[k][i] for k in range(len(pts))) for i in range(W)]
    canon={}; alias={}; 
    canon[tuple([0]*len(pts))]='c0'; canon[tuple([1]*len(pts))]='c1'
    for i in range(n):
        if i!=v: canon.setdefault(tab[i],i)
    for i in range(W):
        if i<n: alias[i]=canon[tab[i]]; continue
        if tab[i] in canon: alias[i]=canon[tab[i]]
        else: canon[tab[i]]=i; alias[i]=i
    need=set(); st=[alias[o] for w,o in enumerate(outs) if (b==0 or v not in S[w])]
    while st:
        i=st.pop()
        if not isinstance(i,int) or i<n or i in need: continue
        need.add(i); st+=[alias[j] for j in G[i-n][1:]]
    return len(need)
def stats(c):
    n,S=c['n'],c['sets']; s=len(c['gates']); best0=best1=-99
    for v in range(n):
        thr=[w for w in S if v in w]
        if not thr: continue
        best0=max(best0,(s-restr(c,v,0))-len(thr))
        best1=max(best1,(s-restr(c,v,1))-sum(len(w)-1 for w in thr))
    return best0,best1
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=load(f); m0=m1=mm=99; n0=n1=nb=0
        for c in cs:
            if c['n']>10: continue
            a,b=stats(c); m0=min(m0,a); m1=min(m1,b); mm=min(mm,max(a,b)); n0+=a<0; n1+=b<0; nb+=max(a,b)<0
        print(f,len(cs),'min over circuits of max_v surplus: x=0:',m0,' x=1:',m1,' either:',mm,'| irreducible by x=0:',n0,'by x=1:',n1,'by both:',nb)
