# weighted gate elimination test: Phi(K)=sum_w min_class (d_w-|cl\K|)^+ ; chains K_0<K_1<...; increments<=1 ?
from sl import *
import collections
cs=allcirc(); st=collections.Counter(); bad=[]
for name,c in cs:
    if c['n']>12: continue
    T,res=classes(c); dem=[len(s)-1 for s in c['sets']]; n=T.n; opts=[]
    for wi,opt in enumerate(res):
        o=set()
        for k,cl in opt.items():
            if k[0]=='1':
                if len(cl[0])>=dem[wi]: o.add(cl[0])
            else: o.add(cl)
        opts.append(list(o))
    def Phi(K): return sum(min(max(0,dem[w]-len(cl-K)) for cl in opts[w]) for w in range(len(dem)))
    gl=list(range(n,T.W)); st['circ']+=1
    for nm,order in (('suffix',gl[::-1]),('prefix',gl)):
        K=set(); prev=0; mx=0; over=0
        for g in order:
            K.add(g); p=Phi(K); mx=max(mx,p-prev); over=max(over,p-len(K)); prev=p
        if mx>1: st[nm+' inc>1']+=1
        if over>0: st[nm+' Phi>|K|']+=1; bad.append((nm,name,over))
    # greedy adaptive: always add gate with smallest increment
    K=set(); prev=0; worst=0
    while len(K)<len(gl):
        best=min((Phi(K|{g}),g) for g in gl if g not in K)
        worst=max(worst,best[0]-prev); prev=best[0]; K.add(best[1])
    if worst>1: st['greedy inc>1']+=1
print(dict(st)); print(bad[:10])
