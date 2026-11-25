from pb import *
import pb
def chain(G,n,ws,op='or'):
    cur=ws[0]
    for w in ws[1:]:
        G.append([op,cur,w]); cur=n+len(G)-1
    return cur
def cxr(k):
    n=2*k; G=[]
    ands=[]
    for i in range(k): G.append(['and',i,i+k]); ands.append(n+len(G)-1)
    h=chain(G,n,ands); G.append(['not',h]); N=n+len(G)-1
    outs=[]
    for S in (range(k),range(k,2*k)):
        t=[]
        for i in S: G.append(['and',N,i]); t.append(n+len(G)-1)
        r=chain(G,n,t); G.append(['or',h,r]); outs.append(n+len(G)-1)
    return dict(n=n,sets=[list(range(k)),list(range(k,2*k))],gates=G,outs=outs)
if __name__=='__main__':
    pb.PS=[0.4,0.5,0.6]
    for k in range(2,7):
        c=cxr(k); T=TT(c); assert T.correct()
        print(k,len(c['gates']),2*(k-1),[round(x,4) for x in pb.run('',c,free=True)],flush=True)
