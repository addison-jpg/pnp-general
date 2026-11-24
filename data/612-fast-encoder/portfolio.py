import multiprocessing as mp, time, sys
import fast_synth as F

def _run(args):
    n,E,k,sym,q=args
    g,r,nr=F.synth_exact(n,E,k,sym=sym)
    q.put((sym,g,r,nr))

def synth_portfolio(n,E,k,levels=(0,1)):
    q=mp.Queue(); ps=[]
    for s in levels:
        p=mp.Process(target=_run,args=((n,E,k,s,q),)); p.start(); ps.append(p)
    res=q.get()                       # first finisher is the answer (SAT or UNSAT both sound)
    for p in ps: p.terminate()
    return res

def min_size_pf(n,E,hi,verbose=True):
    lo=max(1,len(set(u for e in E for u in e))-1)
    for k in range(lo,hi+1):
        t=time.time(); sym,g,r,nr=synth_portfolio(n,E,k)
        if verbose: print(f"   k={k}: {'SAT' if g else 'UNSAT'} {time.time()-t:.1f}s (won by sym={sym})",flush=True)
        if g: return k
if __name__=="__main__":
    Gs={'S3':(7,[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6)]),'C6':(6,[(i,(i+1)%6) for i in range(6)]),'C7':(7,[(i,(i+1)%7) for i in range(7)]),'C5':(5,[(i,(i+1)%5) for i in range(5)])}
    n,E=Gs[sys.argv[1]]; t=time.time()
    print(sys.argv[1],'min=',min_size_pf(n,E,int(sys.argv[2])),'total %.1fs'%(time.time()-t),flush=True)
