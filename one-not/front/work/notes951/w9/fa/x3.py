# apply the X+ choice of each signature to EVERY data circuit: counted sets must be disjoint and >= d (sanity of Theorem X+)
import pickle,sys
sys.path.insert(0,'.')
from lib import *
from sig import down,sig,files
res=pickle.load(open('xplus.pkl','rb'))
tot=0; bad=0; nx=0
for f in files:
    try: cs=load(f)
    except Exception: continue
    for c in cs:
        if not any(g[0]=='not' for g in c['gates']): continue
        s=sig(c); X,P,ch=res[s]
        if X or not P: nx+= (not X); continue
        n=c['n']; d=down(c); cn=[]; tot+=1
        for S,o in zip(c['sets'],ch):
            Q,z1,mono,at=o; atoms={}
            for p,hv in at:
                u=[v for v in p if v in S][0]; atoms[u]=[1 if v in p else 0 for v in range(n)]
            good,wz,B=system(c,S,zQ(n,Q),atoms); assert good or mono
            cn.append({i for i,b in B.items() if i>=n and len(b)>=2 and not (mono and i in d)})
        if sum(map(len,cn))!=len(set().union(*cn)) or any(len(x)<len(S)-1 for x,S in zip(cn,c['sets'])): bad+=1
print('circuits with X+ choice applied',tot,'violations',bad,'circuits with neither X nor X+',nx)
