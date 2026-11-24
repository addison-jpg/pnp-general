import json,sys
from star import analyse,tts
def build(m,k=1):
    # p=0; big sets a_i = {u_i1..u_im}; pair sets {0,u_i1},{0,u_i2}; h = x0
    n=1+m*k; sets=[];G=[]
    def add(g): G.append(g); return n+len(G)-1
    N=add(['not',0]); outs=[]
    for i in range(k):
        S=list(range(1+i*m,1+(i+1)*m)); sets.append(S)
    pouts=[]
    for i,S in enumerate(sets):
        oc=add(['or',0,S[0]]); od=add(['or',0,S[1]]); pouts+=[oc,od]
        K=add(['or',oc,S[1]])
        for u in S[2:]: K=add(['or',K,u])
        M=add(['and',N,K])
        R=None
        for u in S:
            t=add(['and',u,0]); R=t if R is None else add(['or',R,t])
        outs.append(add(['or',M,R]))
    allsets=sets+[[0,S[0]] for S in sets]+[[0,S[1]] for S in sets]
    allouts=outs+pouts[0::2]+pouts[1::2]
    return dict(n=n,sets=allsets,gates=G,outs=allouts)
for m,k in [(4,1),(5,1),(4,2),(6,1),(8,1)]:
    c=build(m,k); r=analyse(c); print(m,k,r)
    if (m,k)==(5,1): json.dump(c,open('cxstar5.json','w'))
    if (m,k)==(4,2): json.dump(c,open('cxstar44.json','w'))
