from cls4 import *
import collections
A=allcirc(); st=collections.Counter(); fails=collections.defaultdict(list); conf=collections.Counter(); cex={}
combos={'A:D1e+D0p':['D1e','D0p'],'B:D1e+D0p+Dr+Pr':['D1e','D0p','Dr','Pr'],'C:D1+D0p':['D1','D0p'],'D:D1+D0p+D0+P0+Dr+Pr':['D1','D0p','D0','P0','Dr','Pr']}
for nm,c in A:
    T=TT(c); m=len(c['sets']); dem=[len(S)-1 for S in c['sets']]; base=sum(dem)
    C=allcls(T)
    for k,cb in combos.items():
        adj=[set().union(*[C[x][i] for x in cb]) for i in range(m)]
        if maxflow_match(dem,adj)<base: st[k]+=1; fails[k].append(nm)
    for i in range(m):
        for j in range(m):
            if i!=j:
                for x in ('D1e','D0p'):
                    for y in ('D1e','D0p'):
                        I=C[x][i]&C[y][j]
                        if I: conf[(x,y)]+=1; cex.setdefault((x,y),(nm,i,j,sorted(I)))
print(st); 
for k,v in fails.items(): print(k,len(v),v[:6])
print(conf,cex)
