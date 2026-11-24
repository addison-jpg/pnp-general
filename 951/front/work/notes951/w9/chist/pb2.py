from pb import *
import pb, time
pb.PS=[0.5,0.75]
names=sys.argv[1:]
cs=[(n,c) for n,c in allcirc()+extra() if any(k in n for k in names) and any(g[0]=='not' for g in c['gates'])]
for name,c in cs:
    t=time.time(); r=pb.run(name,c,free=False); print(name,c['n'],len(c['gates']),sum(len(s)-1 for s in c['sets']),r,round(time.time()-t,1),flush=True)
