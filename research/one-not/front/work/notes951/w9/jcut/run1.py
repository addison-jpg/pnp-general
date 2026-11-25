from cls import *
import sys
A=allcirc()
stat={}
for nm,c in A:
    T=TT(c); sets=c['sets']; dem=[len(S)-1 for S in sets]
    R={}
    for b in ('real',0,1):
        D,P=classes(T,b); R[b]=[D[i]|P[i] for i in range(len(sets))]
    res={}
    res['real']=maxflow_match(dem,R['real'])
    res['w0']=maxflow_match(dem,R[0]); res['w1']=maxflow_match(dem,R[1])
    res['union']=maxflow_match(dem,[R['real'][i]|R[0][i]|R[1][i] for i in range(len(sets))])
    base=sum(dem)
    for k,v in res.items():
        stat.setdefault(k,[0,0]); stat[k][0]+=1; stat[k][1]+= (v<base)
    if res['union']<base or (not nm.startswith('chk') and not nm.startswith('w7')):
        print(nm,'base',base,'s',len(c['gates']),res)
print(stat)
