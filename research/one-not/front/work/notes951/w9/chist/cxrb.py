from cxrk import *
def bal(G,n,ws,op='or'):
    ws=list(ws)
    while len(ws)>1:
        nx=[]
        for i in range(0,len(ws)-1,2):
            G.append([op,ws[i],ws[i+1]]); nx.append(n+len(G)-1)
        if len(ws)%2: nx.append(ws[-1])
        ws=nx
    return ws[0]
def cxrb(k,hb=True,ob=True):
    n=2*k; G=[]
    ands=[]
    for i in range(k): G.append(['and',i,i+k]); ands.append(n+len(G)-1)
    h=(bal if hb else chain)(G,n,ands); G.append(['not',h]); N=n+len(G)-1
    outs=[]
    for S in (range(k),range(k,2*k)):
        t=[]
        for i in S: G.append(['and',N,i]); t.append(n+len(G)-1)
        r=(bal if ob else chain)(G,n,t); G.append(['or',h,r]); outs.append(n+len(G)-1)
    return dict(n=n,sets=[list(range(k)),list(range(k,2*k))],gates=G,outs=outs)
if __name__=='__main__':
    pb.PS=[0.4,0.5,0.6]
    for k,hb,ob in [(4,1,1),(4,1,0),(4,0,1),(5,1,1),(6,1,1),(7,1,1),(8,1,1)]:
        c=cxrb(k,hb,ob); T=TT(c); assert T.correct()
        print(k,hb,ob,len(c['gates']),2*(k-1),[round(x,4) for x in pb.run('',c,free=(k<8))],flush=True)
