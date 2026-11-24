# X-rule test: X_w = Pi_w (private sandwich classes D_w ∪ P_w) ∪ E_w, E_w = gates downstream of the NOT lying in the cone of o_w only.
# rule holds for set w if some menu item has |cnt ∩ X_w| >= d_w  (X_w pairwise disjoint => integral matching, 0/1 price proof).
import sys,json,os,time
import resid as RS
from dualp import roles
def xrule(c, F=None):
    R=roles(c); dem=[len(s)-1 for s in c['sets']]; Dc,Pc=RS.private(c)
    F=F or RS.full(c); out=[]
    allPi=set().union(*Dc,*Pc)
    for w,m in enumerate(F):
        Pi=Dc[w]|Pc[w]
        E={g for g in R if 'aboveN' in R[g]['tags'] and R[g]['cones']==[w]}-allPi
        Ex={g for g in R if R[g]['cones']==[w]}-allPi
        best=max(m,key=lambda it:(len(set(it[0])&(Pi|E)),len(set(it[0])&(Pi|Ex))))
        C=set(best[0])
        out.append(dict(w=w,d=dem[w],pi=max(len(set(it[0])&Pi) for it in m),x=len(C&(Pi|E)),xx=max(len(set(it[0])&(Pi|Ex)) for it in m),hz=best[2],z=[i for i,b in enumerate(best[1]) if b],
                        used=sorted(C&(Pi|E)),PiE=(sorted(Pi),sorted(E))))
    return out
if __name__=='__main__':
    for f in sys.argv[1:]:
        cs=[json.loads(l) for l in open(f)] if f.endswith('.jsonl') else [json.load(open(f))]
        for i,c in enumerate(cs):
            t=time.time(); o=xrule(c)
            bad=[r['w'] for r in o if r['x']<r['d']]
            print(os.path.basename(f),i,'sets',c['sets'],'XRULE','FAIL %s'%bad if bad else 'ok','%.1fs'%(time.time()-t))
            for r in o: print('    set %d d=%d |Pi∩cnt|max=%d |X∩cnt|=%d (excl-cone any: %d) world h(z)=%d z=%s used=%s'%(r['w'],r['d'],r['pi'],r['x'],r['xx'],r['hz'],r['z'],r['used']))
