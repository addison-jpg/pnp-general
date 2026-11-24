# V1 / V2 for WHOLE world-1 unit classes cl_w = {g in M : g(0,1)=0, g(e_u,1)=1 for >=2 u in S_w} (same configuration as M_w)
import json, sys, glob, random
from ref import tts, norm, check
from extra import genH5, mf
from adv import forest_system, build, shuffle_topo
def whole(c):
    c=norm(c); n=c['n']; G=c['gates']; S=c['sets']; var,W,o,FULL=tts(c); W1=W[1]
    Ni=[n+k for k,g in enumerate(G) if g[0]=='not'][0]
    cl=[]
    for Sx in S:
        cl.append([n+k for k in range(len(G)) if n+k!=Ni and not W1[n+k]&1 and sum(W1[n+k]>>(1<<u)&1 for u in Sx)>=2])
    dem=[len(x)-1 for x in S]; base=sum(dem); U=set().union(*map(set,cl)); sM=len(G)-1
    fl=mf(dem,cl); return dict(sM=sM,base=base,U=len(U),sumcl=sum(map(len,cl)),V2=sM-sum(map(len,cl)),V1=(sM-len(U))-(base-fl),flow=fl)
if __name__=='__main__':
    for k,m in [(2,4),(3,3),(3,4),(4,3),(5,2)]:
        c=genH5(k,m); print('genH5',k,m,whole(c))
    rng=random.Random(5); worst=None; nf=0; v1bad=0; v2bad=0
    for it in range(3000):
        n=rng.randint(4,10); sets=forest_system(n,rng,False)
        if len(sets)<2: continue
        c=build(n,sets,rng,'th2')
        if c is None: continue
        c=shuffle_topo(c,rng); r,v=check(c)
        if not (r['correct'] and r['ess'] and r['cyc']==0): continue
        nf+=1; w=whole(c); v1bad+=w['V1']<0; v2bad+=w['V2']<0
        if worst is None or w['V1']<worst[0]['V1']: worst=(w,c)
    print('forest ess circuits',nf,'whole-class V1<0:',v1bad,'V2<0:',v2bad,'worst',worst[0]); json.dump(worst[1],open('whole_worst.json','w'))
