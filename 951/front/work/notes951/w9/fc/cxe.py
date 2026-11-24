# cxE: cxtw sunflower + h' = x0 | h_sun, plus sets E=inner, F=outer (N-sets via cx1-style gadget) to kill all families.
import json, sys
from lib import *
from clean import cleanup
def build(t, EF=('E','F'), gadget=False):
    n=2*t+1+(2 if gadget else 0); G=[]
    def g(op,a,b=None):
        G.append([op,a,b] if op!='not' else ['not',a]); return n+len(G)-1
    def AND(ws):
        w=ws[0]
        for v in ws[1:]: w=g('and',w,v)
        return w
    def OR(ws):
        w=ws[0]
        for v in ws[1:]: w=g('or',w,v)
        return w
    main=list(range(2*t+1)); sets=[[0,i,i+t] for i in range(1,t+1)]
    hs=OR([AND([v for v in main if v not in S]) for S in sets]); h=g('or',0,hs); N=g('not',h)
    A=1; L=None
    for k in range(2,t+1):
        if L is None: L=g('or',1,2); A=g('and',1,2)
        else: L=g('or',g('and',L,k),A); A=g('and',A,k)
    T=g('and',AND(list(range(t+1,2*t+1))),L)
    GG=g('or',0,T); outs=[]
    for i in range(1,t+1): outs.append(g('or',GG,g('or',i,g('and',i+t,N))))
    def gad(P):
        p=g('or',OR([g('and',P[0],h)]+P[1:]),N); q=OR([g('or',P[0],h)]+P[1:]); return g('and',p,q)
    if 'E' in EF: sets.append(list(range(1,t+1))); outs.append(gad(sets[-1]))
    if 'F' in EF: sets.append(list(range(t+1,2*t+1))); outs.append(gad(sets[-1]))
    if gadget: sets.append([2*t+1,2*t+2]); outs.append(gad(sets[-1]))
    return dict(n=n,sets=sets,gates=G,outs=outs)
if __name__=='__main__':
    t=int(sys.argv[1]); c=cleanup(build(t)); json.dump(c,open('cxe%d.json'%t,'w')); report(c, full=len(sys.argv)>2)
