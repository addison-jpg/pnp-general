# Candidate counterexample to TWO-WORLD HALL: sunflower S_i={0,i,i+t}, h = OR_i AND_{v main, v notin S_i} x_v,
# T = AND(x_{t+1..2t}) & Th_{t-1}(x_1..x_t) (T <= h), G = x0|T, o_i = G | (x_i | (x_{i+t} & N)); gadget set {a,b} (cx1).
import json, sys
def build(t, gadget=True):
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
    h=OR([AND([v for v in main if v not in S]) for S in sets]); N=g('not',h)
    # Th_{t-1}(x1..xt): at most one zero: prefix L_k (<=1 zero among first k), A_k (all ones among first k)
    A=1; L=None
    for k in range(2,t+1):
        if L is None: L=g('or',1,2); A=g('and',1,2)
        else:
            L=g('or',g('and',L,k),A); A=g('and',A,k)
    if t==2: L=g('or',1,2)
    T=g('and',AND(list(range(t+1,2*t+1))),L)
    GG=g('or',0,T); outs=[]
    for i in range(1,t+1):
        outs.append(g('or',GG,g('or',i,g('and',i+t,N))))
    if gadget:
        a,b=2*t+1,2*t+2; sets.append([a,b])
        p=g('or',g('or',g('and',a,h),b),N); q=g('or',g('or',a,h),b); outs.append(g('and',p,q))
    return dict(n=n,sets=sets,gates=G,outs=outs)
if __name__=='__main__':
    t=int(sys.argv[1]); c=build(t, len(sys.argv)<3); print(json.dumps(c))
