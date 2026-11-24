from sl import *
from chk2 import lp
import collections
cs=allcirc(); st=collections.Counter(); ex=[]
for name,c in cs:
    if c['n']>12: continue
    T,res=classes(c); dem=[len(s)-1 for s in c['sets']]; opts=[]; single=0
    for wi,opt in enumerate(res):
        o=set()
        for k,cl in opt.items():
            if k[0]=='1':
                if len(cl[0])>=dem[wi]: o.add(cl[0])
            else: o.add(cl)
        U=set().union(*o); single=max(single,dem[wi]/len(U))
        opts.append([x for x in o if not any(y<x for y in o)])
    L,pi,lam=lp(dem,opts)
    supp=[g for g,p in pi.items() if p>1e-9]; vals={round(pi[g],6) for g in supp}
    st['all']+=1
    if abs(L-single)<1e-7: st['single-set tight']+=1
    else: st['interaction']+=1; ex.append((round(L,4),round(single,4),name,len(supp),sorted(vals)))
    st['uniform pi' if len(vals)==1 else 'nonuniform pi']+=1
print(dict(st)); 
for e in sorted(ex,reverse=True)[:12]: print(e)
