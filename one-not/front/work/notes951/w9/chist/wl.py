# whole-class (Chistikov) LP on the lifted menu: max sum_e y_e d_e  s.t. every gate load sum_{e: g in cl_e} y_e <= 1
import sys, glob, json, collections
S='/tmp/claude-0/-home-user/c6907e1a-c924-52ad-8144-e086bc36ec3a/scratchpad/'
sys.path.insert(0,S+'w9/s'); sys.path.insert(0,S+'w9/jcut')
from lift import *
from bt import norm
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def extra():
    out=[]
    for f in sorted(glob.glob(S+'w9/p/cxP*.json'))+sorted(glob.glob(S+'w9/g3/cx*.json'))+sorted(glob.glob(S+'w9/srepay_ref/*.json'))+sorted(glob.glob(S+'w9/srepay/hand_*.json')):
        try:
            c=json.load(open(f))
            if isinstance(c,dict) and 'gates' in c: out.append((f.replace(S,''),norm(c)))
            elif isinstance(c,list):
                for i,cc in enumerate(c):
                    if isinstance(cc,dict) and 'gates' in cc: out.append((f.replace(S,'')+':%d'%i,norm(cc)))
        except Exception as e: print('skip',f,e)
    for f in ['w7/k4h5_4.jsonl','w7/k4h5_5.jsonl','w7/k4worst.jsonl']:
        for i,l in enumerate(open(S+f)):
            if l.strip():
                try: out.append((f+':%d'%i,norm(json.loads(l))))
                except Exception: pass
    return out
def wlp(dem,opts,normalize=False):
    ents=[(w,C) for w,m in enumerate(opts) for C in m]
    gates=sorted({g for _,C in ents for g in C}); gi={g:i for i,g in enumerate(gates)}
    rows=len(gates)+(len(dem) if normalize else 0)
    A=lil_matrix((rows,len(ents)))
    for j,(w,C) in enumerate(ents):
        for g in C: A[gi[g],j]=1
        if normalize: A[len(gates)+w,j]=1
    res=linprog([-dem[w] for w,_ in ents],A_ub=A.tocsr(),b_ub=np.ones(rows),bounds=[(0,None)]*len(ents),method='highs')
    return -res.fun,{ents[j]:res.x[j] for j in range(len(ents)) if res.x[j]>1e-9}
def run(name,c):
    T=TT(c)
    if not T.correct(): return None
    dem=[len(s)-1 for s in c['sets']]
    opts=[menu(T,c,wi)[0] for wi in range(len(dem))]
    a,_=wlp(dem,opts); b,_=wlp(dem,opts,True)
    return a,b,sum(dem),len(c['gates'])
if __name__=='__main__':
    cs=allcirc()+extra(); print(len(cs)); res=[]
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    for name,c in cs:
        if not (lo<=c['n']<=hi) or not any(g[0]=='not' for g in c['gates']): continue
        r=run(name,c)
        if r is None: print('INCORRECT',name); continue
        res.append((r[0]-r[2],r[1]-r[2],r,name))
    res.sort(); print(len(res)); 
    print('worst unnormalized WL-base:',res[:8])
    res.sort(key=lambda t:t[1]); print('worst normalized:',res[:8])
    print(collections.Counter(round(t[1],3) for t in res).most_common(10))
    print('unnorm<base:',sum(1 for t in res if t[0]<-1e-7),'norm<base:',sum(1 for t in res if t[1]<-1e-7))
