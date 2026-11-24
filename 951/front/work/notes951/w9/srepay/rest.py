# decomposition s-1 = |J| + #AND + #OR(1 at (0,1)) + #OR(in V, not joint merge); compare with base-|J| <= cyc
import sys, collections, json
sys.argv=['x']
from analyze import *
from bt import allcirc
def decomp(T):
    w=world1_merges(T); n=T.n; J=set(w['J']); V=set(w['V'])
    nand=sum(1 for g in T.GL if T.G[g-n][0]=='and')
    ndepand=sum(1 for g in T.GL if T.G[g-n][0]=='and' and T.w[0][g]!=T.w[1][g])
    hi=sum(1 for g in T.GL if T.G[g-n][0]=='or' and g not in V)
    red=sum(1 for g in T.GL if T.G[g-n][0]=='or' and g in V and g not in J)
    return dict(J=len(J),AND=nand,ANDy=ndepand,HI=hi,RED=red,cyc=w['cyc'],coll=w['coll'],X=len(w['X']),sM=len(T.GL))
if __name__=='__main__':
    st=collections.Counter(); mins=[]
    for name,c in allcirc():
        T=info(norm(c)); d=decomp(T); base=sum(len(s)-1 for s in c['sets'])
        ess=essential(T)
        if ess and d['ANDy']==0: st['ESS_NO_YAND']+=1
        st['ess' if ess else 'iness']+=1
        mins.append((d['AND']+d['HI']+d['RED']-d['cyc'], d['AND'], d['cyc'], name))
    mins.sort(); print(dict(st)); print('min (rest - cyc):',mins[:6])
    print('min #AND among essential:',min((m[1],m[3]) for m in mins))
