# Counterexample to Hall (canonical choice). vars 0..8: a={0,1,2,3}, b={0,4,5,6}, c={7,8}; h=OR(1..6)
import sys, json, itertools
sys.path.insert(0,'../chk'); sys.argv=sys.argv[:1]
import chargeok_check as K
n=9; G=[]
def add(op,*a): G.append([op,*a]); return n+len(G)-1
p1=add('or',1,4); p2=add('or',2,5); p3=add('or',3,6)
g=add('or',p1,p2); h=add('or',g,p3); N=add('not',h); g2=add('or',h,0)
r=add('or',0,N)
ka=r
for v in (1,2,3): ka=add('or',ka,v)
kb=r
for v in (4,5,6): kb=add('or',kb,v)
oa=add('and',g2,ka); ob=add('and',g2,kb)
t=add('and',7,h); A=add('or',t,8); AN=add('or',A,N); t2=add('or',7,h); B=add('or',t2,8); oc=add('and',AN,B)
c={'n':n,'sets':[[0,1,2,3],[0,4,5,6],[7,8]],'gates':G,'outs':[oa,ob,oc]}
json.dump(c,open('cx1.json','w'))
print(c, 's',len(G),'base',7)
# correctness, essential, clean, read
S=c['sets']; tabs=[[] for _ in range(n+len(G))]
def evalN(x,force=None):
    w=list(x)
    for gt in G:
        if gt[0]=='not': w.append(1-w[gt[1]] if force is None else force)
        elif gt[0]=='and': w.append(w[gt[1]]&w[gt[2]])
        else: w.append(w[gt[1]]|w[gt[2]])
    return w
ok=True; c0=True; c1=True
for x in itertools.product([0,1],repeat=n):
    w=evalN(x); w0=evalN(x,0); w1=evalN(x,1)
    for i in range(len(w)): tabs[i].append(w[i])
    for o,st in zip(c['outs'],S):
        f=int(any(x[v] for v in st)); ok&=w[o]==f; c0&=w0[o]==f; c1&=w1[o]==f
print('correct',ok,'C0 correct',c0,'C1 correct',c1)
tt=[tuple(t) for t in tabs]
print('clean (all wire functions distinct, nonconstant):',len(set(tt))==len(tt), all(0<sum(t)<len(t) for t in tt))
read=set(j for gt in G for j in gt[1:])|set(c['outs'])
print('all gates read or output:',all(n+k in read for k in range(len(G))))
import importlib; 
src=open('../chk/hallcheck.py').read().split('H=Counter()')[0]
import os; os.chdir('../chk'); exec(src)
Ds=canon(c); print('canonical cnt',Ds, 'union',len(set().union(*map(set,Ds))),'bmatch',bmatch(Ds,[3,3,1]))
print('family {a,b}: union',len(set(Ds[0])|set(Ds[1])),'need 6')
