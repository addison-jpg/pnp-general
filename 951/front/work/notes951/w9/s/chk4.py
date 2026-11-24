# lifted single-domain configurations: coverage + privacy checks with random atoms
from sl import *
import random, collections
random.seed(1)
def pts(T,R,u,Q):  # points p in U1 with p∩Q={u}
    n=T.n; rest=[v for v in range(n) if v not in Q]; out=[]
    for r in range(len(rest)+1):
        for zz in itertools.combinations(rest,r):
            p=(1<<u)|sum(1<<v for v in zz)
            if (T.h>>p)&1 and not any((q&p)==q for q in out): out.append(p)
        if len(out)>6: break
    return out
def val(T,g,at):  # at=(p,level)
    return (T.w[at[1]][g]>>at[0])&1
cs=allcirc(); st=collections.Counter()
for name,c in cs:
    if c['n']>10: continue
    T,_=classes(c); n=T.n; gates=range(n,T.W); S=c['sets']; cfg=[]
    for wi,R in enumerate(S):
        d=len(R)-1; no=T.FULL^T.o[wi]; mine=[]
        # type 0
        P={u:pts(T,R,u,R) for u in R}
        miss=[u for u in R if not P[u]]
        if len(miss)<=1:
            G0=[g for g in gates if (T.w[0][g]&no)==0]
            for _ in range(4):
                at={u:((random.choice(P[u]),0) if P[u] else (1<<u,1)) for u in R}
                if not miss and random.random()<0.3:
                    u0=random.choice(R); at[u0]=(1<<u0,1)
                cl=frozenset(g for g in G0 if sum(val(T,g,at[u]) for u in R)>=2)
                st['t0']+=1
                if len(cl)<d: st['t0short']+=1; print('T0 SHORT',name,wi,at)
                mine.append((0,None,at,cl))
        # type 1
        rest=[v for v in range(n) if v not in R]
        for _ in range(4):
            zz=[v for v in rest if random.random()<0.5]; cpt=sum(1<<v for v in zz)
            if (T.h>>cpt)&1: continue
            Q=[v for v in range(n) if not cpt>>v&1]
            at={}
            for u in R:
                P1=pts(T,R,u,Q)
                at[u]=(random.choice(P1),0) if (P1 and random.random()<0.5) else (1<<u,1)
            cl=frozenset(g for g in gates if not (T.w[1][g]>>cpt)&1 and sum(val(T,g,at[u]) for u in R)>=2)
            st['t1']+=1
            if len(cl)<d: st['t1short']+=1; print('T1 SHORT',name,wi,cpt,at)
            mine.append((1,cpt,at,cl))
        cfg.append(mine)
    # privacy: lifted X+ rule
    def below(at,cf,wb):  # is atom in down-closure of Z of config cf of set wb
        p,l=at
        if cf[0]==0: return l==0 and not any(p>>v&1 for v in S[wb])
        return (p&cf[1])==p   # p<=c (any level)
    for a in range(len(S)):
        for b in range(a+1,len(S)):
            for ca in cfg[a]:
                for cb in cfg[b]:
                    I=ca[3]&cb[3]
                    if not I: continue
                    st['coll']+=1
                    Pab=sum(1 for u in S[a] if not below(ca[2][u],cb,b)); Pba=sum(1 for u in S[b] if not below(cb[2][u],ca,a))
                    if Pab<=1 or Pba<=1: st['PRIV VIOL']+=1; print('VIOL',name,a,b)
print(dict(st))
