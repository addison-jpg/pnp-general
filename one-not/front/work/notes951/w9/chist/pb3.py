from pb import *
import pb, time, json, glob
pb.PS=[0.5]
files=sys.argv[3:]; lo,hi=int(sys.argv[1]),int(sys.argv[2])
tot=0; worst=(0,''); bad=[]; skipped=0; t0=time.time()
for f in files:
    L=[norm(json.loads(l)) for l in open(S+f) if l.strip()][lo:hi]
    for i,c in enumerate(L):
        if not any(g[0]=='not' for g in c['gates']): skipped+=1; continue
        r=pb.run(f,c,free=False)
        if r is None: skipped+=1; continue
        tot+=1
        if r[0]>worst[0]: worst=(r[0],'%s:%d'%(f,lo+i))
        if r[0]>1+1e-7: bad.append(('%s:%d'%(f,lo+i),r[0]))
    print(f,'done',tot,'worst',worst,'bad',len(bad),'skipped',skipped,round(time.time()-t0),flush=True)
print(bad[:20])
