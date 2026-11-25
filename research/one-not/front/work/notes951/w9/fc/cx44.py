# two 4-sets a={0123}, b={0456}, h = x1x2 | x4x5; world-0 merge tree g1,g2,g3 SHARED (g3 = OR(S_a) on {x4x5=1}, OR(S_b) on {x1x2=1});
# world-1 chains polluted by h (rule-invisible).  o_a = (N & Wa) | x1x2 | (x4x5 & g3)
import json, sys
from tri5 import *
def build(pollute=True):
    n=7; G=[]
    def g(op,a,b=None):
        G.append([op,a,b] if op!='not' else ['not',a]); return n+len(G)-1
    m12=g('and',1,2); m45=g('and',4,5); h=g('or',m12,m45); N=g('not',h)
    g1=g('or',0,g('and',g('and',1,4),g('or',5,2)))
    g2=g('or',g1,g('and',g('and',2,5),g('or',4,1)))
    g3=g('or',g2,g('or',g('and',m45,3),g('and',m12,6)))
    def W(L):
        w=g('or',h,L[0]) if pollute else L[0]
        for v in L[1:]: w=g('or',w,v)
        return w
    oa=g('or',g('or',g('and',N,W([0,1,2,3])),m12),g('and',m45,g3))
    ob=g('or',g('or',g('and',N,W([0,4,5,6])),m45),g('and',m12,g3))
    return dict(n=n,sets=[[0,1,2,3],[0,4,5,6]],gates=G,outs=[oa,ob])
if __name__=='__main__':
    from lib import fraclp, family, hbmatch, canon, rstar, mix
    for pol in (True,False):
        c=build(pol); json.dump(c,open('cx44_%d.json'%pol,'w')); print('pollute',pol,bverify(c),'family',family(c))
        rel=brel(c); dem=[3,3]
        for s,r in zip(c['sets'],rel): print(' set',s,'P',r['P'],'menu',r['menu'])
        M=[{frozenset(C):(z,None) for z,C in r['menu'].items() if len(C)>=d} for r,d in zip(rel,dem)]
        print(' L_rel =', 'inf' if any(not m for m in M) else fraclp(c,M=M)[0])
        print(' canonical',hbmatch(canon(c),dem),'R*',hbmatch(rstar(c),dem),'coin',mix(c,.5),'FULL L* all-gate',fraclp(c,False)[0],'coneonly',fraclp(c,True)[0])
