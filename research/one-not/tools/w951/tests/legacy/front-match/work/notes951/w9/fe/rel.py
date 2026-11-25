# relative sandwich classes I_z(w): check conflict lemma E1 and coverage
import sys, json, itertools
sys.path.insert(0,'../fa')
from lib import load, ev, nw, hw
def tt(c):
    n,G=c['n'],c['gates']
    return [ev(n,G,[(x>>i)&1 for i in range(n)]) for x in range(1<<n)]   # T[x][wire]
def analyse(c, maxw=2):
    n,G,S,outs=c['n'],c['gates'],c['sets'],c['outs']; T=tt(c); H=hw(c); N=nw(c); W=n+len(G)
    gates=[i for i in range(n,W) if i!=N]
    full=(1<<n)-1
    def orS(S_,x): return int(any((x>>u)&1 for u in S_))
    # P_w: g>=OR(S_w), g not const 1, g not >= OR(S_j) j!=w
    ge=[[all(T[x][g]>=orS(Sj,x) for x in range(1<<n)) for Sj in S] for g in range(W)]
    nonconst=[any(T[x][g]==0 for x in range(1<<n)) for g in range(W)]
    P=[{g for g in gates+[N] if ge[g][w] and nonconst[g] and not any(ge[g][j] for j in range(len(S)) if j!=w)} for w in range(len(S))]
    # candidate z
    ones=[x for x in range(1<<n) if T[x][H]==1]
    minh=[x for x in ones if bin(x).count('1')<=maxw and not any(T[x&~(1<<i)][H] for i in range(n) if (x>>i)&1)]
    cls={}
    for w,Sw in enumerate(S):
        m=sum(1<<u for u in Sw)
        for z in [0]+[x for x in minh if x&m==0]:
            cnt=[g for g in range(n,W) if T[z][g]==0 and sum(T[z|(1<<u)][g] for u in Sw)>=2]
            sup=[x for x in range(1<<n) if x&z==z]
            low={g for g in cnt if all(T[x][g]<=orS(Sw,x) for x in sup)}
            up={g for g in cnt if g in P[w]}
            cls[(w,z)]=(low,up)
    return cls,T,H
def check(c):
    n,S=c['n'],c['sets']; cls,T,H=analyse(c); bad=0; coll=0
    keys=list(cls)
    for a in keys:
        for b in keys:
            if a[0]>=b[0]: continue
            (w,z),(w2,z2)=a,b
            la,ua=cls[a]; lb,ub=cls[b]
            if (ua&(lb|ub)) or (ub&la): bad+=1; print('UPPER VIOL',a,b)
            I=la&lb
            if I:
                coll+=1
                m1=sum(1<<u for u in S[w]); m2=sum(1<<u for u in S[w2])
                def side(z,z2,Sw,mo):  # z hits S_other or crossing at z-side
                    if z&mo: return True
                    return any(T[z|(1<<u)][H]==0 and T[z|z2|(1<<u)][H]==1 for u in Sw)
                if not(side(z,z2,S[w],m2) and side(z2,z,S[w2],m1)): bad+=1; print('E1 VIOL',a,b,I)
    # coverage: best z per set
    dem=[len(s)-1 for s in S]
    best=[max(len(l|u) for (w,z),(l,u) in cls.items() if w==i) for i in range(len(S))]
    return bad,coll,[b-d for b,d in zip(best,dem)]
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=load(f); tb=tc=0; short=0
        for k,c in enumerate(cs):
            if c['n']>10: continue
            b,co,sl=check(c); tb+=b; tc+=co; short+= any(x<0 for x in sl)
            if len(cs)<=3: print(f,'bad',b,'collisions',co,'slack best|I|-d',sl)
        print(f,'circuits',len(cs),'violations',tb,'collision pairs',tc,'circuits with a short set',short)
