from mg import *
import mg, time
files=sys.argv[3:]; lo,hi=int(sys.argv[1]),int(sys.argv[2]); tot=0; bad=[]; an=0; t0=time.time()
for f in files:
    if f.endswith('.jsonl'): L=[norm(json.loads(l)) for l in open(S+f) if l.strip()][lo:hi]
    else: L=[norm(json.load(open(f if f.startswith('/') or f.startswith('cx') else S+f)))]
    for i,c in enumerate(L):
        if not any(g[0]=='not' for g in c['gates']): continue
        r=mg.run(f,c)
        if r is None: continue
        tot+=1; an+=r[1]>0
        if r[0]>1+1e-7: bad.append((f,lo+i,r[0]))
        if len(L)==1: print(f,c['n'],r,flush=True)
    print(f,'tot',tot,'bad',len(bad),'anom',an,round(time.time()-t0),flush=True)
print(bad[:10])
