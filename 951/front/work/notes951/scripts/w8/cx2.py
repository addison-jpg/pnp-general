# sunflower, n=7: S_i={0,i,i+3}; h=OR(1..6); essential without extra set
import sys, json, itertools
n=7; G=[]
def add(op,*a): G.append([op,*a]); return n+len(G)-1
A=add('or',1,2); A2=add('or',A,3); B=add('or',4,5); B2=add('or',B,6); h=add('or',A2,B2); N=add('not',h)
g2=add('or',h,0); t=add('and',0,h); r=add('or',N,t); outs=[]
for i in (1,2,3):
    k=add('or',r,i); k=add('or',k,i+3); outs.append(add('and',g2,k))
c={'n':n,'sets':[[0,1,4],[0,2,5],[0,3,6]],'gates':G,'outs':outs}
json.dump(c,open('cx2.json','w')); print(c,'s',len(G))
