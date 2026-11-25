# junk counterexample to rule R*: inner-product design. S_a={0,1,2,3}, S_b={4,5,6,7}, h=t=OR_i x_i x_{i+4}
import json,itertools,sys
from rstar import *
n=8; G=[]
def add(op,*a): G.append([op,*a]); return n+len(G)-1
pr=[add('and',i,i+4) for i in range(4)]
t=add('or',add('or',pr[0],pr[1]),add('or',pr[2],pr[3])); N=add('not',t)
def k(S):
    m=[add('and',N,u) for u in S]; return add('or',add('or',m[0],m[1]),add('or',m[2],m[3]))
oa=add('or',t,k([0,1,2,3])); ob=add('or',t,k([4,5,6,7]))
c={'n':n,'sets':[[0,1,2,3],[4,5,6,7]],'gates':G,'outs':[oa,ob]}
json.dump(c,open('cxr.json','w'))
ok=c0=c1=True; tabs=[[] for _ in range(n+len(G))]
for x in itertools.product([0,1],repeat=n):
    w=ev(n,G,x)
    for i,v in enumerate(w): tabs[i].append(v)
    for o,S in zip(c['outs'],c['sets']): ok&= w[o]==int(any(x[v] for v in S))
    for force in (0,1):
        G2=[g if g[0]!='not' else ['and',0,0] for g in G]  # placeholder
    # C0/C1
    for force,name in ((0,'c0'),(1,'c1')):
        w2=list(x)
        for g in G:
            if g[0]=='not': w2.append(force)
            elif g[0]=='and': w2.append(w2[g[1]]&w2[g[2]])
            else: w2.append(w2[g[1]]|w2[g[2]])
        good=all(w2[o]==int(any(x[v] for v in S)) for o,S in zip(c['outs'],c['sets']))
        if force==0: c0&=good
        else: c1&=good
tt=[tuple(t_) for t_ in tabs]
print('correct',ok,'C0 ok',c0,'C1 ok',c1,'clean',len(set(tt))==len(tt),'s',len(G))
Ds=rstar(c); dem=[3,3]; print('R* cnt',Ds,'union',len(set(Ds[0])|set(Ds[1])),'match',bmatch(Ds,dem))
# full Sigma(z) menu
best=0; wins=[]
men=[]
for wi,S in enumerate(c['sets']):
    rest=[v for v in range(n) if v not in S]; m={}
    for zm in itertools.product([0,1],repeat=len(rest)):
        z=[0]*n
        for v,b in zip(rest,zm): z[v]=b
        m[tuple(z)]=cnt_z(c,wi,z)
    men.append(m)
tot=full=0
for za,Da in men[0].items():
    for zb,Db in men[1].items():
        tot+=1; f=bmatch([Da,Db],dem)==6; full+=f
        if f and len(wins)<3: wins.append((za,Da,zb,Db))
print('Sigma(z) pairs',tot,'full',full); print(wins)
