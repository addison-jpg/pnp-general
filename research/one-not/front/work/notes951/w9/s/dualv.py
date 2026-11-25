from sl import *
from chk2 import lp
import sys, json
def run(name,c,verbose=True):
    T,res=classes(c); dem=[len(s)-1 for s in c['sets']]; opts=[];keys=[]
    for wi,opt in enumerate(res):
        o={}
        for k,cl in opt.items():
            if k[0]=='1':
                if len(cl[0])>=dem[wi]: o.setdefault(cl[0],k)
            else: o.setdefault(cl,k)
        ks=[x for x in o if not any(y<x for y in o)]
        opts.append(ks); keys.append([o[x] for x in ks])
    L,pi,lam=lp(dem,opts)
    if verbose:
        print(name,'n',c['n'],'s',len(c['gates']),'base',sum(dem),'L*',round(L,4),'hard',T.hard)
        print(' pi:',{g:round(p,3) for g,p in pi.items() if p>1e-9}, 'ndep',sorted(T.ndep))
        for (w,j),x in sorted(lam.items()): print('  set',w,c['sets'][w],'lam',round(x,3),keys[w][j][0],bin(keys[w][j][1]) if len(keys[w][j])>1 else '',sorted(opts[w][j]))
    return L,pi,lam,T
if __name__=='__main__':
    for f in sys.argv[1:]:
        for c in load(f)[:1]: run(f,c)
