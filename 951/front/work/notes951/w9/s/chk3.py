from sl import *
from chk2 import lp
import collections
def strict0(T,c,wi,z,cl):
    R=c['sets'][wi]; cube=T.FULL
    for v in range(T.n):
        if z>>v&1: cube&=T.var[v]
    bad=cube&(T.FULL^T.o[wi])
    return frozenset(g for g in cl if (T.w[1][g]&bad)==0)
def strictE(T,c,wi,cl):
    R=c['sets'][wi]
    return frozenset(g for g in cl if sum((T.w[0][g]>>(1<<u))&1 for u in R)>=2)
if __name__=='__main__':
    cs=allcirc(); st=collections.Counter(); worst=[]
    for name,c in cs:
        if c['n']>12: continue
        T,res=classes(c); dem=[len(s)-1 for s in c['sets']]; opts=[]; ok=True
        for wi,opt in enumerate(res):
            o=set(); d=dem[wi]
            if T.hard[wi]:
                st['hard']+=1
                s0=[strict0(T,c,wi,k[1],cl) for k,cl in opt.items() if k[0]=='0']
                best0=max(len(x) for x in s0)
                w1=[cl[0] for k,cl in opt.items() if k[0]=='1' and len(cl[0])>=d]
                if best0>=d: st['hard_strict0_ok']+=1
                if w1: st['hard_w1_ok']+=1
                if best0<d and not w1: st['hard_none']+=1; ok=False; st['minshort',d-best0]+=1
                o={x for x in s0 if len(x)>=d}|set(w1)
            else:
                st['easy']+=1; cl=opt[('E',)]; o={cl}
                if len(strictE(T,c,wi,cl))>=d: st['easy_strict_ok']+=1
            opts.append([x for x in o if not any(y<x for y in o)])
        if not ok: st['circ_uncovered']+=1; continue
        L,pi,lam=lp(dem,opts); worst.append((L,name))
    worst.sort(reverse=True); print(dict(st)); print(worst[:8]); print(collections.Counter(round(L,3) for L,_ in worst).most_common(8))
